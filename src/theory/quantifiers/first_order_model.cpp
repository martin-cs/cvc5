/*********************                                                        */
/*! \file first_order_model.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of model engine model class
 **/

#include "theory/quantifiers/first_order_model.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "theory/quantifiers/fmf/full_model_check.h"
#include "theory/quantifiers/fmf/model_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/term_util.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory::quantifiers::fmcheck;

namespace CVC4 {
namespace theory {
namespace quantifiers {

struct sortQuantifierRelevance {
  FirstOrderModel * d_fm;
  bool operator() (Node i, Node j) {
    int wi = d_fm->getRelevanceValue( i );
    int wj = d_fm->getRelevanceValue( j );
    if( wi==wj ){
      return i<j;
    }else{
      return wi<wj;
    }
  }
};

RepSetIterator::RsiEnumType QRepBoundExt::setBound(Node owner,
                                                   unsigned i,
                                                   std::vector<Node>& elements)
{
  // builtin: check if it is bound by bounded integer module
  if (owner.getKind() == FORALL && d_qe->getBoundedIntegers())
  {
    if (d_qe->getBoundedIntegers()->isBoundVar(owner, owner[0][i]))
    {
      unsigned bvt =
          d_qe->getBoundedIntegers()->getBoundVarType(owner, owner[0][i]);
      if (bvt != BoundedIntegers::BOUND_FINITE)
      {
        d_bound_int[i] = true;
        return RepSetIterator::ENUM_BOUND_INT;
      }
      else
      {
        // indicates the variable is finitely bound due to
        // the (small) cardinality of its type,
        // will treat in default way
      }
    }
  }
  return RepSetIterator::ENUM_INVALID;
}

bool QRepBoundExt::resetIndex(RepSetIterator* rsi,
                              Node owner,
                              unsigned i,
                              bool initial,
                              std::vector<Node>& elements)
{
  if (d_bound_int.find(i) != d_bound_int.end())
  {
    Assert(owner.getKind() == FORALL);
    Assert(d_qe->getBoundedIntegers() != nullptr);
    if (!d_qe->getBoundedIntegers()->getBoundElements(
            rsi, initial, owner, owner[0][i], elements))
    {
      return false;
    }
  }
  return true;
}

bool QRepBoundExt::initializeRepresentativesForType(TypeNode tn)
{
  return d_qe->getModel()->initializeRepresentativesForType(tn);
}

bool QRepBoundExt::getVariableOrder(Node owner, std::vector<unsigned>& varOrder)
{
  // must set a variable index order based on bounded integers
  if (owner.getKind() == FORALL && d_qe->getBoundedIntegers())
  {
    Trace("bound-int-rsi") << "Calculating variable order..." << std::endl;
    for (unsigned i = 0; i < d_qe->getBoundedIntegers()->getNumBoundVars(owner);
         i++)
    {
      Node v = d_qe->getBoundedIntegers()->getBoundVar(owner, i);
      Trace("bound-int-rsi") << "  bound var #" << i << " is " << v
                             << std::endl;
      varOrder.push_back(d_qe->getTermUtil()->getVariableNum(owner, v));
    }
    for (unsigned i = 0; i < owner[0].getNumChildren(); i++)
    {
      if (!d_qe->getBoundedIntegers()->isBoundVar(owner, owner[0][i]))
      {
        varOrder.push_back(i);
      }
    }
    return true;
  }
  return false;
}

FirstOrderModel::FirstOrderModel(QuantifiersEngine * qe, context::Context* c, std::string name ) :
TheoryModel( c, name, true ),
d_qe( qe ), d_forall_asserts( c ){
  d_rlv_count = 0;
}

void FirstOrderModel::assertQuantifier( Node n ){
  if( n.getKind()==FORALL ){
    d_forall_asserts.push_back( n );
  }else if( n.getKind()==NOT ){
    Assert( n[0].getKind()==FORALL );
  }
}

unsigned FirstOrderModel::getNumAssertedQuantifiers() { 
  return d_forall_asserts.size(); 
}

Node FirstOrderModel::getAssertedQuantifier( unsigned i, bool ordered ) { 
  if( !ordered ){
    return d_forall_asserts[i]; 
  }else{
    Assert( d_forall_rlv_assert.size()==d_forall_asserts.size() );
    return d_forall_rlv_assert[i];
  }
}

void FirstOrderModel::initialize() {
  processInitialize( true );
  //this is called after representatives have been chosen and the equality engine has been built
  //for each quantifier, collect all operators we care about
  for( unsigned i=0; i<getNumAssertedQuantifiers(); i++ ){
    Node f = getAssertedQuantifier( i );
    if( d_quant_var_id.find( f )==d_quant_var_id.end() ){
      for(unsigned j=0; j<f[0].getNumChildren(); j++){
        d_quant_var_id[f][f[0][j]] = j;
      }
    }
    processInitializeQuantifier( f );
    //initialize relevant models within bodies of all quantifiers
    std::map< Node, bool > visited;
    initializeModelForTerm( f[1], visited );
  }
  processInitialize( false );
}

void FirstOrderModel::initializeModelForTerm( Node n, std::map< Node, bool >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    processInitializeModelForTerm( n );
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      initializeModelForTerm( n[i], visited );
    }
  }
}

Node FirstOrderModel::getSomeDomainElement(TypeNode tn){
  //check if there is even any domain elements at all
  if (!d_rep_set.hasType(tn) || d_rep_set.d_type_reps[tn].size() == 0)
  {
    Trace("fm-debug") << "Must create domain element for " << tn << "..."
                      << std::endl;
    Node mbt = getModelBasisTerm(tn);
    Trace("fm-debug") << "Add to representative set..." << std::endl;
    d_rep_set.add(tn, mbt);
  }
  return d_rep_set.d_type_reps[tn][0];
}

bool FirstOrderModel::initializeRepresentativesForType(TypeNode tn)
{
  if (tn.isSort())
  {
    // must ensure uninterpreted type is non-empty.
    if (!d_rep_set.hasType(tn))
    {
      // terms in rep_set are now constants which mapped to terms through
      // TheoryModel. Thus, should introduce a constant and a term.
      // For now, we just add an arbitrary term.
      Node var = d_qe->getModel()->getSomeDomainElement(tn);
      Trace("mkVar") << "RepSetIterator:: Make variable " << var << " : " << tn
                     << std::endl;
      d_rep_set.add(tn, var);
    }
    return true;
  }
  else
  {
    // can we complete it?
    if (d_qe->getTermEnumeration()->mayComplete(tn))
    {
      Trace("fm-debug") << "  do complete, since cardinality is small ("
                        << tn.getCardinality() << ")..." << std::endl;
      d_rep_set.complete(tn);
      // must have succeeded
      Assert(d_rep_set.hasType(tn));
      return true;
    }
    Trace("fm-debug") << "  variable cannot be bounded." << std::endl;
    return false;
  }
}

/** needs check */
bool FirstOrderModel::checkNeeded() {
  return d_forall_asserts.size()>0;
}

void FirstOrderModel::reset_round() {
  d_quant_active.clear();
  
  //order the quantified formulas
  d_forall_rlv_assert.clear();
  if( !d_forall_rlv_vec.empty() ){
    Trace("fm-relevant") << "Build sorted relevant list..." << std::endl;
    Trace("fm-relevant-debug") << "Mark asserted quantified formulas..." << std::endl;
    std::map< Node, bool > qassert;
    for( unsigned i=0; i<d_forall_asserts.size(); i++ ){
      qassert[d_forall_asserts[i]] = true;
    }
    Trace("fm-relevant-debug") << "Sort the relevant quantified formulas..." << std::endl;
    sortQuantifierRelevance sqr;
    sqr.d_fm = this;
    std::sort( d_forall_rlv_vec.begin(), d_forall_rlv_vec.end(), sqr );
    Trace("fm-relevant-debug") << "Add relevant asserted formulas..." << std::endl;
    for( int i=(int)(d_forall_rlv_vec.size()-1); i>=0; i-- ){
      Node q = d_forall_rlv_vec[i];
      if( qassert.find( q )!=qassert.end() ){
        Trace("fm-relevant") << "   " << d_forall_rlv[q] << " : " << q << std::endl;
        d_forall_rlv_assert.push_back( q );
      }
    }
    Trace("fm-relevant-debug") << "Add remaining asserted formulas..." << std::endl;
    for( unsigned i=0; i<d_forall_asserts.size(); i++ ){
      Node q = d_forall_asserts[i];
      if( std::find( d_forall_rlv_assert.begin(), d_forall_rlv_assert.end(), q )==d_forall_rlv_assert.end() ){
        d_forall_rlv_assert.push_back( q );
      }else{
        Trace("fm-relevant-debug") << "...already included " << q << std::endl;
      }
    }
    Trace("fm-relevant-debug") << "Sizes : " << d_forall_rlv_assert.size() << " " << d_forall_asserts.size() << std::endl;
    Assert( d_forall_rlv_assert.size()==d_forall_asserts.size() );
  }else{
    for( unsigned i=0; i<d_forall_asserts.size(); i++ ){
      d_forall_rlv_assert.push_back( d_forall_asserts[i] );
    }
  }
}

void FirstOrderModel::markRelevant( Node q ) {
  if( q!=d_last_forall_rlv ){
    Trace("fm-relevant") << "Mark relevant : " << q << std::endl;
    if( std::find( d_forall_rlv_vec.begin(), d_forall_rlv_vec.end(), q )==d_forall_rlv_vec.end() ){
      d_forall_rlv_vec.push_back( q );
    }
    d_forall_rlv[ q ] = d_rlv_count;
    d_rlv_count++;
    d_last_forall_rlv = q;
  }
}

int FirstOrderModel::getRelevanceValue( Node q ) {
  std::map< Node, unsigned >::iterator it = d_forall_rlv.find( q );
  if( it==d_forall_rlv.end() ){
    return -1;
  }else{
    return it->second;
  }
}

void FirstOrderModel::setQuantifierActive( TNode q, bool active ) {
  d_quant_active[q] = active;
}

bool FirstOrderModel::isQuantifierActive( TNode q ) {
  std::map< TNode, bool >::iterator it = d_quant_active.find( q );
  if( it==d_quant_active.end() ){
    return true;
  }else{
    return it->second;
  }
}

bool FirstOrderModel::isQuantifierAsserted( TNode q ) {
  Assert( d_forall_rlv_assert.size()==d_forall_asserts.size() );
  return std::find( d_forall_rlv_assert.begin(), d_forall_rlv_assert.end(), q )!=d_forall_rlv_assert.end();
}

Node FirstOrderModel::getModelBasisTerm(TypeNode tn)
{
  if (d_model_basis_term.find(tn) == d_model_basis_term.end())
  {
    Node mbt;
    if (tn.isClosedEnumerable())
    {
      mbt = d_qe->getTermEnumeration()->getEnumerateTerm(tn, 0);
    }
    else
    {
      if (options::fmfFreshDistConst())
      {
        mbt = d_qe->getTermDatabase()->getOrMakeTypeFreshVariable(tn);
      }
      else
      {
        mbt = d_qe->getTermDatabase()->getOrMakeTypeGroundTerm(tn);
      }
    }
    ModelBasisAttribute mba;
    mbt.setAttribute(mba, true);
    d_model_basis_term[tn] = mbt;
    Trace("model-basis-term") << "Choose " << mbt << " as model basis term for "
                              << tn << std::endl;
  }
  return d_model_basis_term[tn];
}

bool FirstOrderModel::isModelBasisTerm(Node n)
{
  return n == getModelBasisTerm(n.getType());
}

Node FirstOrderModel::getModelBasisOpTerm(Node op)
{
  if (d_model_basis_op_term.find(op) == d_model_basis_op_term.end())
  {
    TypeNode t = op.getType();
    std::vector<Node> children;
    children.push_back(op);
    for (int i = 0; i < (int)(t.getNumChildren() - 1); i++)
    {
      children.push_back(getModelBasisTerm(t[i]));
    }
    if (children.size() == 1)
    {
      d_model_basis_op_term[op] = op;
    }
    else
    {
      d_model_basis_op_term[op] =
          NodeManager::currentNM()->mkNode(APPLY_UF, children);
    }
  }
  return d_model_basis_op_term[op];
}

Node FirstOrderModel::getModelBasis(Node q, Node n)
{
  // make model basis
  if (d_model_basis_terms.find(q) == d_model_basis_terms.end())
  {
    for (unsigned j = 0; j < q[0].getNumChildren(); j++)
    {
      d_model_basis_terms[q].push_back(getModelBasisTerm(q[0][j].getType()));
    }
  }
  Node gn = d_qe->getTermUtil()->substituteInstConstants(
      n, q, d_model_basis_terms[q]);
  return gn;
}

void FirstOrderModel::computeModelBasisArgAttribute(Node n)
{
  if (!n.hasAttribute(ModelBasisArgAttribute()))
  {
    // ensure that the model basis terms have been defined
    if (n.getKind() == APPLY_UF)
    {
      getModelBasisOpTerm(n.getOperator());
    }
    uint64_t val = 0;
    // determine if it has model basis attribute
    for (unsigned j = 0, nchild = n.getNumChildren(); j < nchild; j++)
    {
      if (n[j].getAttribute(ModelBasisAttribute()))
      {
        val++;
      }
    }
    ModelBasisArgAttribute mbaa;
    n.setAttribute(mbaa, val);
  }
}

unsigned FirstOrderModel::getModelBasisArg(Node n)
{
  computeModelBasisArgAttribute(n);
  return n.getAttribute(ModelBasisArgAttribute());
}

FirstOrderModelFmc::FirstOrderModelFmc(QuantifiersEngine * qe, context::Context* c, std::string name) :
FirstOrderModel(qe, c, name){

}

FirstOrderModelFmc::~FirstOrderModelFmc()
{
  for(std::map<Node, Def*>::iterator i = d_models.begin(); i != d_models.end(); ++i) {
    delete (*i).second;
  }
}

void FirstOrderModelFmc::processInitialize( bool ispre ) {
  if( ispre ){
    for( std::map<Node, Def * >::iterator it = d_models.begin(); it != d_models.end(); ++it ){
      it->second->reset();
    }
  }
}

void FirstOrderModelFmc::processInitializeModelForTerm(Node n) {
  if( n.getKind()==APPLY_UF ){
    if( d_models.find(n.getOperator())==d_models.end()) {
      d_models[n.getOperator()] = new Def;
    }
  }
}


bool FirstOrderModelFmc::isStar(Node n) {
  //return n==getStar(n.getType());
  return n.getAttribute(IsStarAttribute());
}

Node FirstOrderModelFmc::getStar(TypeNode tn) {
  std::map<TypeNode, Node >::iterator it = d_type_star.find( tn );
  if( it==d_type_star.end() ){
    Node st = NodeManager::currentNM()->mkSkolem( "star", tn, "skolem created for full-model checking" );
    d_type_star[tn] = st;
    st.setAttribute(IsStarAttribute(), true );
    return st;
  }
  return it->second;
}

Node FirstOrderModelFmc::getFunctionValue(Node op, const char* argPrefix ) {
  Trace("fmc-model") << "Get function value for " << op << std::endl;
  TypeNode type = op.getType();
  std::vector< Node > vars;
  for( size_t i=0; i<type.getNumChildren()-1; i++ ){
    std::stringstream ss;
    ss << argPrefix << (i+1);
    Node b = NodeManager::currentNM()->mkBoundVar( ss.str(), type[i] );
    vars.push_back( b );
  }
  Node boundVarList = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, vars);
  Node curr;
  for( int i=(d_models[op]->d_cond.size()-1); i>=0; i--) {
    Node v = d_models[op]->d_value[i];
    Trace("fmc-model-func") << "Value is : " << v << std::endl;
    Assert( v.isConst() );
    /*
    if( !hasTerm( v ) ){
      //can happen when the model basis term does not exist in ground assignment
      TypeNode tn = v.getType();
      //check if it is a constant introduced as a representative not existing in the model's equality engine
      if( !d_rep_set.hasRep( tn, v ) ){
        if( d_rep_set.d_type_reps.find( tn )!=d_rep_set.d_type_reps.end() && !d_rep_set.d_type_reps[ tn ].empty() ){
          v = d_rep_set.d_type_reps[tn][ d_rep_set.d_type_reps[tn].size()-1 ];
        }else{
          //can happen for types not involved in quantified formulas
          Trace("fmc-model-func") << "No type rep for " << tn << std::endl;
          v = d_qe->getTermUtil()->getEnumerateTerm( tn, 0 );
        }
        Trace("fmc-model-func") << "No term, assign " << v << std::endl;
      }
    }
    v = getRepresentative( v );
    */
    if( curr.isNull() ){
      Trace("fmc-model-func") << "base : " << v << std::endl;
      curr = v;
    }else{
      //make the condition
      Node cond = d_models[op]->d_cond[i];
      Trace("fmc-model-func") << "...cond : " << cond << std::endl;
      std::vector< Node > children;
      for( unsigned j=0; j<cond.getNumChildren(); j++) {
        TypeNode tn = vars[j].getType();
        if (!isStar(cond[j]))
        {
          Node c = getRepresentative( cond[j] );
          c = getRepresentative( c );
          children.push_back( NodeManager::currentNM()->mkNode( EQUAL, vars[j], c ) );
        }
      }
      Assert( !children.empty() );
      Node cc = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( AND, children );

      Trace("fmc-model-func") << "condition : " << cc << ", value : " << v << std::endl;
      curr = NodeManager::currentNM()->mkNode( ITE, cc, v, curr );
    }
  }
  Trace("fmc-model") << "Made " << curr << " for " << op << std::endl;
  curr = Rewriter::rewrite( curr );
  return NodeManager::currentNM()->mkNode(kind::LAMBDA, boundVarList, curr);
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
