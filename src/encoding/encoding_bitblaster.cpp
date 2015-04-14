/*********************                                                        */
/*! \file encoding_bitblaster.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bitblaster for the lazy bv solver. 
 **
 ** Bitblaster for the lazy bv solver. 
 **/

#include "cvc4_private.h"
#include "theory/bv/bitblaster_template.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/options.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_factory.h"
#include "theory/theory_model.h"
#include "theory/bv/abstraction.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv; 


EncodingBitblaster::EncodingBitblaster(context::Context* c, const std::string name)
  : TBitblaster<Node>()
  , d_ctx(c)
  , d_assertedAtoms(new(true) context::CDList<CVC4::prop::SatLiteral>(c))
  , d_variables()
  , d_bbAtoms()
  , d_satSolverFullModel(c, false)
  , d_name(name)
  , d_statistics(name) {
  d_satSolver = new CVC4::prop::EMinisatSatSolver(c, name);
  d_nullRegistrar = new CVC4::prop::NullRegistrar();
  d_nullContext = new context::Context();
  d_cnfStream = new CVC4::prop::TseitinCnfStream(d_satSolver,
						 d_nullRegistrar,
						 d_nullContext, true);
  
  d_satSolverNotify = NULL;
  // FIXME: encoding hack for debugging 
  d_atomBBStrategies [ kind::IFF ] = DefaultIffBB<Node>;
  d_atomBBStrategies [ kind::SKOLEM ] = DefaultSkolemBB<Node>;
}

bool EncodingBitblaster::EncodingNotify::notify(CVC4::prop::SatLiteral lit) {
  TNode theory_lit = d_cnf_this->getNode(lit);
  Debug("encoding-detailed") << "EncodingNotify::notify<" << d_lazyBB->getName()
			     <<">" << theory_lit << std::endl;
  ++d_numTotalPropagations;
  // mark literals that the other solver also had internally
  if (d_cnf_other->hasLiteral(theory_lit)) {
    Debug("encoding-detailed") << "EncodingNotify::notify<" << d_lazyBB->getName()
		      <<"> shared " << theory_lit << std::endl;
    d_propagated.insert(theory_lit);
    ++d_numSharedPropagations;
  }
  return true;
}

void EncodingBitblaster::EncodingNotify::notify(CVC4::prop::SatClause& clause) {
  // TODO
  // maybe check if we learn the same clauses?
}

void EncodingBitblaster::clearLearnedClauses() {
  d_satSolver->clearLearned();
}

int EncodingBitblaster::getNumLearnedClauses() {
  return d_satSolver->getNumLearned();
}
int EncodingBitblaster::getNumProblemClauses() {
  return d_satSolver->getNumClauses();
}


void EncodingBitblaster::printLearned(std::ostream& out) {
  int n = d_satSolver->getNumLearned();
  for (int i = 0; i < n; ++i) {
    CVC4::prop::SatClause cl;
    d_satSolver->getLearnedClause(i, cl);
    
    for (unsigned i = 0; i < cl.size(); ++i) {
      out << cl[i].toString() << " ";
    }
    out << std::endl;
    for (unsigned i = 0; i < cl.size(); ++i) {
        out << d_cnfStream->getNode(cl[i]) << " ";
    }
    out << std::endl;
  }
}

void EncodingBitblaster::printCnfMapping(std::ostream& out, const NodeSet& toprint) {
  // out << "c "<< getName() << std::endl;
  const CVC4::prop::CnfStream::LiteralToNodeMap& map = d_cnfStream->getNodeCache();
  CVC4::prop::CnfStream::LiteralToNodeMap::const_iterator it = map.begin();
  unsigned num_lits = 0 ;
  unsigned num_skolems = 0;
  for (; it != map.end(); ++it) {
    CVC4::prop::SatLiteral lit = it->first;

    if (lit.isNegated()) continue;
    
    TNode node = it->second;
    if (!toprint.empty()) {
      if (toprint.find(node) != toprint.end()) {
	out << "c " << lit.toString() <<" : " << node << std::endl;
      } else {
        out << "c " << lit.toString() << " : n" << node.getId() << std::endl;
	//out << "c " << lit.toString() <<" : x[" << num_skolems<<"]" << std::endl;
	++num_skolems;
      }
    } else {
      out << "c " << lit.toString() <<" : " << node << std::endl;
    }
    ++num_lits;
  }
  out << "p cnf " << num_lits <<" ";
}

void EncodingBitblaster::printProblemClauses(std::ostream& out) {
  int n = d_satSolver->getNumClauses();
  out << n << std::endl;
  for (int i = 0; i < n; ++i) {
    CVC4::prop::SatClause cl;
    d_satSolver->getProblemClause(i, cl);
    
    for (unsigned i = 0; i < cl.size(); ++i) {
      out << cl[i].toString() << " ";
    //   out << d_cnfStream->getNode(cl[i]) << " ";
    }
    out << "0" << std::endl;
  }
}


void EncodingBitblaster::assertFact(TNode node) {
  TNode atom = node.getKind() == kind::NOT?  node[0] : node;

  Debug("bitvector-bitblast") << "Bitblasting node " << node <<"\n";
  /// if we are using bit-vector abstraction bit-blast the original interpretation
  // the bitblasted definition of the atom
  Node normalized = atom;
  Node atom_bb = normalized.getKind() != kind::CONST_BOOLEAN ?
    d_atomBBStrategies[normalized.getKind()](normalized, this) :
    normalized;
  atom_bb = Rewriter::rewrite(atom_bb);
  atom_bb = node.getKind() == kind::NOT? utils::mkNode(kind::NOT, atom_bb) : atom_bb;
  d_cnfStream->convertAndAssert(atom_bb, false, false, RULE_INVALID, TNode::null());
}

void EncodingBitblaster::assumeLiteral(TNode lit) {
  TNode atom;
  Debug("encoding-detailed") << "EncodingBitblaster::assumeLiteral<" << getName() <<"> "
		    << lit << std::endl;

  if (lit.getKind() == kind::NOT) {
    atom = lit[0];
  } else {
    atom = lit;
  }

  CVC4::prop::SatLiteral satLit = d_cnfStream->getLiteral(atom);

  if(lit.getKind() == kind::NOT) {
    satLit = ~satLit;
  }

  CVC4::prop::SatValue ret = d_satSolver->assertAssumption(satLit, false);
  Assert(ret == CVC4::prop::SAT_VALUE_TRUE);
  d_assertedAtoms->push_back(satLit);
}

void EncodingBitblaster::setNotify(EncodingBitblaster::EncodingNotify* en) {
  AlwaysAssert (d_satSolverNotify == NULL);
  d_satSolverNotify = (CVC4::prop::EncodingSatSolverInterface::Notify*) en;
  d_satSolver->setNotify(d_satSolverNotify);  
}

EncodingBitblaster::~EncodingBitblaster() {
  delete d_cnfStream;
  delete d_nullRegistrar;
  delete d_nullContext;
  delete d_satSolver;
  d_assertedAtoms->deleteSelf();
}



/**
 * Bitblasts the atom, assigns it a marker literal, adding it to the SAT solver
 * NOTE: duplicate clauses are not detected because of marker literal
 * @param node the atom to be bitblasted
 *
 */
void EncodingBitblaster::bbAtom(TNode node) {
  node = node.getKind() == kind::NOT?  node[0] : node;

  if (hasBBAtom(node)) {
    return;
  }

  Debug("bitvector-bitblast") << "Bitblasting node " << node <<"\n";
  ++d_statistics.d_numAtoms;

  // the bitblasted definition of the atom
  Node normalized = node;
  Node atom_bb = normalized.getKind() != kind::CONST_BOOLEAN ?
    Rewriter::rewrite(d_atomBBStrategies[normalized.getKind()](normalized, this)) :
    normalized;
  // asserting that the atom is true iff the definition holds
  Node atom_definition = utils::mkNode(kind::IFF, node, atom_bb);
  storeBBAtom(node, atom_bb);
  d_cnfStream->convertAndAssert(atom_definition, false, false, RULE_INVALID, TNode::null());
}

void EncodingBitblaster::storeBBAtom(TNode atom, Node atom_bb) {
  // no need to store the definition for the lazy bit-blaster
  d_bbAtoms.insert(atom); 
}

bool EncodingBitblaster::hasBBAtom(TNode atom) const {
  return d_bbAtoms.find(atom) != d_bbAtoms.end(); 
}


void EncodingBitblaster::makeVariable(TNode var, Bits& bits) {
  Assert(bits.size() == 0);
  for (unsigned i = 0; i < utils::getSize(var); ++i) {
    bits.push_back(utils::mkBitOf(var, i)); 
  }
  d_variables.insert(var); 
}

// cnf conversion ensures the atom represents itself
Node EncodingBitblaster::getBBAtom(TNode node) const {
  return node; 
}

void EncodingBitblaster::bbTerm(TNode node, Bits& bits) {

  if (hasBBTerm(node)) {
    getBBTerm(node, bits);
    return;
  }

  Debug("bitvector-bitblast") << "Bitblasting node " << node <<"\n";
  ++d_statistics.d_numTerms;

  d_termBBStrategies[node.getKind()] (node, bits,this);

  Assert (bits.size() == utils::getSize(node));

  storeBBTerm(node, bits);
}
/// Public methods

void EncodingBitblaster::addAtom(TNode atom) {
  d_cnfStream->ensureLiteral(atom);
  CVC4::prop::SatLiteral lit = d_cnfStream->getLiteral(atom);
  d_satSolver->addMarkerLiteral(lit);
}

/*
 * Asserts the clauses corresponding to the atom to the Sat Solver
 * by turning on the marker literal (i.e. setting it to false)
 * @param node the atom to be asserted
 *
 */

bool EncodingBitblaster::propagate() {
  return d_satSolver->propagate() == CVC4::prop::SAT_VALUE_TRUE;
}

/**
 * Calls the solve method for the Sat Solver.
 * passing it the marker literals to be asserted
 *
 * @return true for sat, and false for unsat
 */

bool EncodingBitblaster::solve() {
  if (Trace.isOn("bitvector")) {
    Trace("bitvector") << "EncodingBitblaster::solve() asserted atoms ";
    context::CDList<CVC4::prop::SatLiteral>::const_iterator it = d_assertedAtoms->begin();
    for (; it != d_assertedAtoms->end(); ++it) {
      Trace("bitvector") << "     " << d_cnfStream->getNode(*it) << "\n";
    }
  }
  Debug("bitvector") << "EncodingBitblaster::solve() asserted atoms " << d_assertedAtoms->size() <<"\n";
  d_satSolverFullModel.set(true);
  CVC4::prop::SatValue res = d_satSolver->solve();
  Assert (res != CVC4::prop::SAT_VALUE_UNKNOWN); 
  return CVC4::prop::SAT_VALUE_TRUE == res;
}

CVC4::prop::SatValue EncodingBitblaster::solveWithBudget(unsigned long budget) {
  if (Trace.isOn("bitvector")) {
    Trace("bitvector") << "EncodingBitblaster::solveWithBudget() asserted atoms ";
    context::CDList<CVC4::prop::SatLiteral>::const_iterator it = d_assertedAtoms->begin();
    for (; it != d_assertedAtoms->end(); ++it) {
      Trace("bitvector") << "     " << d_cnfStream->getNode(*it) << "\n";
    }
  }
  Debug("bitvector") << "EncodingBitblaster::solveWithBudget() asserted atoms " << d_assertedAtoms->size() <<"\n";
  return d_satSolver->solve(budget);
}


void EncodingBitblaster::getConflict(std::vector<TNode>& conflict) {
  CVC4::prop::SatClause conflictClause;
  d_satSolver->getUnsatCore(conflictClause);

  for (unsigned i = 0; i < conflictClause.size(); i++) {
    CVC4::prop::SatLiteral lit = conflictClause[i];
    TNode atom = d_cnfStream->getNode(lit);
    Node  not_atom;
    if (atom.getKind() == kind::NOT) {
      not_atom = atom[0];
    } else {
      not_atom = NodeManager::currentNM()->mkNode(kind::NOT, atom);
    }
    conflict.push_back(not_atom);
  }
}

EncodingBitblaster::Statistics::Statistics(const std::string& prefix) :
  d_numTermClauses("theory::bv::"+prefix+"::NumberOfTermSatClauses", 0),
  d_numAtomClauses("theory::bv::"+prefix+"::NumberOfAtomSatClauses", 0),
  d_numTerms("theory::bv::"+prefix+"::NumberOfBitblastedTerms", 0),
  d_numAtoms("theory::bv::"+prefix+"::NumberOfBitblastedAtoms", 0),
  d_numExplainedPropagations("theory::bv::"+prefix+"::NumberOfExplainedPropagations", 0),
  d_numBitblastingPropagations("theory::bv::"+prefix+"::NumberOfBitblastingPropagations", 0),
  d_bitblastTimer("theory::bv::"+prefix+"::BitblastTimer")
{
  StatisticsRegistry::registerStat(&d_numTermClauses);
  StatisticsRegistry::registerStat(&d_numAtomClauses);
  StatisticsRegistry::registerStat(&d_numTerms);
  StatisticsRegistry::registerStat(&d_numAtoms);
  StatisticsRegistry::registerStat(&d_numExplainedPropagations);
  StatisticsRegistry::registerStat(&d_numBitblastingPropagations);
  StatisticsRegistry::registerStat(&d_bitblastTimer);
}


EncodingBitblaster::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_numTermClauses);
  StatisticsRegistry::unregisterStat(&d_numAtomClauses);
  StatisticsRegistry::unregisterStat(&d_numTerms);
  StatisticsRegistry::unregisterStat(&d_numAtoms);
  StatisticsRegistry::unregisterStat(&d_numExplainedPropagations);
  StatisticsRegistry::unregisterStat(&d_numBitblastingPropagations);
  StatisticsRegistry::unregisterStat(&d_bitblastTimer);
}



bool EncodingBitblaster::hasValue(TNode a) {
  Assert (hasBBTerm(a)); 
  Bits bits;
  getBBTerm(a, bits); 
  for (int i = bits.size() -1; i >= 0; --i) {
    CVC4::prop::SatValue bit_value;
    if (d_cnfStream->hasLiteral(bits[i])) {
      CVC4::prop::SatLiteral bit = d_cnfStream->getLiteral(bits[i]);
      bit_value = d_satSolver->value(bit);
      if (bit_value ==  CVC4::prop::SAT_VALUE_UNKNOWN)
        return false;
    } else {
      return false;
    }
  }
  return true;
}
/**
 * Returns the value a is currently assigned to in the SAT solver
 * or null if the value is completely unassigned.
 *
 * @param a
 * @param fullModel whether to create a "full model," i.e., add
 * constants to equivalence classes that don't already have them
 *
 * @return
 */
Node EncodingBitblaster::getModelFromSatSolver(TNode a, bool fullModel) {
  if (utils::isVar(a) && a.getType().isBoolean()) {
    CVC4::prop::SatLiteral bit = d_cnfStream->getLiteral(a);
    CVC4::prop::SatValue bit_value = d_satSolver->value(bit);
    if (bit_value == CVC4::prop::SAT_VALUE_TRUE) {
      return utils::mkTrue();
    } else if (bit_value == CVC4::prop::SAT_VALUE_FALSE) {
      return utils::mkFalse();
    }
    return fullModel? utils::mkFalse() : Node();
  }
  
  if (!hasBBTerm(a)) {
    return fullModel? utils::mkConst(utils::getSize(a), 0u) : Node();
  }
  
  Bits bits;
  getBBTerm(a, bits);
  Integer value(0);
  for (int i = bits.size() -1; i >= 0; --i) {
    CVC4::prop::SatValue bit_value;
    if (d_cnfStream->hasLiteral(bits[i])) {
      CVC4::prop::SatLiteral bit = d_cnfStream->getLiteral(bits[i]);
      bit_value = d_satSolver->value(bit);
      Assert (bit_value != CVC4::prop::SAT_VALUE_UNKNOWN);
    } else {
      if (!fullModel) return Node();
      // unconstrained bits default to false
      bit_value = CVC4::prop::SAT_VALUE_FALSE;
    }
    Integer bit_int = bit_value == CVC4::prop::SAT_VALUE_TRUE ? Integer(1) : Integer(0);
    value = value * 2 + bit_int;
  }
  return utils::mkConst(BitVector(bits.size(), value));
}

