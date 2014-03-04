#include "theory/fp/theory_fp.h"

#include "theory/fp/trp_integration.h"


using namespace std;

namespace CVC4 {
namespace theory {
namespace fp {

/** Constructs a new instance of TheoryFp w.r.t. the provided contexts. */
TheoryFp::TheoryFp(context::Context* c,
                           context::UserContext* u,
                           OutputChannel& out,
                           Valuation valuation,
                           const LogicInfo& logicInfo) :
  Theory(THEORY_FP, c, u, out, valuation, logicInfo),
  floatingPointConstants(u),
  roundingModeConstants(u),
  floatingPointVariables(u),
  floatingPointOperations(u),
  floatingPointConversions(u),
  floatingPointRelations(u)
{
}/* TheoryFp::TheoryFp() */

void TheoryFp::preRegisterTerm(TNode node) {
  Trace("fp") << "TheoryFp::preRegisterTerm(): " << node << std::endl;

  switch (node.getKind()) {
  /******** Constants ********/
  case kind::CONST_FLOATINGPOINT :
    floatingPointConstants.insert(node);
    break;
  case kind::CONST_ROUNDINGMODE :
    roundingModeConstants.insert(node);
    break;
    
  /******** Variables ********/
  case kind::VARIABLE :
  case kind::BOUND_VARIABLE :
  case kind::SELECT :         // Support array reasoning, \todo check
    if (node.getType().isFloatingPoint()) {
      floatingPointVariables.insert(node);
    } else {
      Assert(node.getType().isRoundingMode());
      Unimplemented("Variable rounding modes not supported");
    }
    break;
    
  /******** Operations ********/
  case kind::FLOATINGPOINT_ABS :
  case kind::FLOATINGPOINT_NEG :
  case kind::FLOATINGPOINT_PLUS :
  case kind::FLOATINGPOINT_MULT :
  case kind::FLOATINGPOINT_DIV :
  case kind::FLOATINGPOINT_FMA :
  case kind::FLOATINGPOINT_SQRT :
  case kind::FLOATINGPOINT_REM :
  case kind::FLOATINGPOINT_RTI :
  case kind::FLOATINGPOINT_MIN :
  case kind::FLOATINGPOINT_MAX :
    floatingPointOperations.insert(node);
    break;
    
  /******** Comparisons ********/
  case kind::EQUAL : 
  case kind::FLOATINGPOINT_EQ :
  case kind::FLOATINGPOINT_LEQ :
  case kind::FLOATINGPOINT_LT :
  case kind::FLOATINGPOINT_ISN :
  case kind::FLOATINGPOINT_ISSN :
  case kind::FLOATINGPOINT_ISZ :
  case kind::FLOATINGPOINT_ISINF :
  case kind::FLOATINGPOINT_ISNAN :
    floatingPointRelations.insert(node);
    break;
    
  /******** Conversions ********/
  case kind::FLOATINGPOINT_FP :
  case kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR :
  case kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT : 
  case kind::FLOATINGPOINT_TO_FP_REAL : 
  case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR :
  case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR :
    Unimplemented("Conversions to floating-point from non-literal values not supported.");
    floatingPointConversions.insert(node);
    break;

  case kind::FLOATINGPOINT_TO_UBV : 
  case kind::FLOATINGPOINT_TO_SBV : 
  case kind::FLOATINGPOINT_TO_REAL :
    Unimplemented("Conversions from non-literal floating-point values not supported.");
    break;


  case kind::FLOATINGPOINT_SUB :
  case kind::FLOATINGPOINT_GEQ :
  case kind::FLOATINGPOINT_GT :
    Unreachable("Kind should have been removed by rewriter.");

  case kind::FLOATINGPOINT_TYPE : 
    Unreachable("Floating-point type when operation expected?");
  default :
    Unhandled(node.getKind());
    break;
  }

}/* TheoryFp::preRegisterTerm() */





void TheoryFp::check(Effort level) {

  Trace("fp") << "TheoryFp::check(" << level << ") called" << std::endl;

  // Only call once the Boolean part has been decided
  if (level >= EFFORT_FULL) {

    // DO NOT REMOVE!
    // The CVC4 build system needs at least one non-macro usage of
    // each debug and trace tag for the build to recognise these as valid
    Trace("TRP") << "TRP trace enabled" << std::endl;
    Debug("TRP") << "TRP debug enabled" << std::endl;

    AbstractElementWithTrail astate;
    Transformer trans(astate);
    std::vector<Assignment> clause;


    // Populate the abstract domain with variables
    Trace("fp") << "Adding variables to the abstract domain" << std::endl;
    for (NodeSet::const_iterator i = floatingPointVariables.begin();
	 i != floatingPointVariables.end();
	 ++i) {
      astate.add(*i);
    }

    // For conveninence, add constants as domain elements as well.
    Trace("fp") << "Adding constants to the abstract domain" << std::endl;
    for (NodeSet::const_iterator i = floatingPointConstants.begin();
	 i != floatingPointConstants.end();
	 ++i) {
      astate.add(*i);

      // Add clauses to fix it's value
      const FloatingPointLiteral &val((*i).getConst<FloatingPoint>().getLiteral());
      
      if (val.isNaN()) {
	clause.clear();
	clause.push_back(CartesianAssignment(*i,true));
	((ClauseDB &)trans).add(TRP::createDisjunction<AbstractElementWithTrail>(clause));
	
	clause.clear();
	clause.push_back(CartesianAssignment(*i,TRP::meetIrreducible< TRP::interval< CVC4::FloatingPointLiteral > >(+INFINITY, false)));
	((ClauseDB &)trans).add(TRP::createDisjunction<AbstractElementWithTrail>(clause));

	clause.clear();
	clause.push_back(CartesianAssignment(*i,TRP::meetIrreducible< TRP::interval< CVC4::FloatingPointLiteral > >(-INFINITY, true)));
	((ClauseDB &)trans).add(TRP::createDisjunction<AbstractElementWithTrail>(clause));

      } else {
	clause.clear();
	clause.push_back(CartesianAssignment(*i,false));
	((ClauseDB &)trans).add(TRP::createDisjunction<AbstractElementWithTrail>(clause));
	
	clause.clear();
	clause.push_back(CartesianAssignment(*i,TRP::meetIrreducible< TRP::interval< CVC4::FloatingPointLiteral > >(val, false)));
	((ClauseDB &)trans).add(TRP::createDisjunction<AbstractElementWithTrail>(clause));

	clause.clear();
	clause.push_back(CartesianAssignment(*i,TRP::meetIrreducible< TRP::interval< CVC4::FloatingPointLiteral > >(val, true)));
	((ClauseDB &)trans).add(TRP::createDisjunction<AbstractElementWithTrail>(clause));

      }
    }


    // Create the transformer and populate both it and the abstract
    // domain with operators
    Trace("fp") << "Adding operations" << std::endl;
    for (NodeSet::const_iterator i = floatingPointOperations.begin();
	 i != floatingPointOperations.end();
	 ++i) {
      astate.add(*i);
      ((Expressions &)trans).add(TRP::createCVC4Term<AbstractElementWithTrail>(*i));

      // Some operations imply auxillary constraints
      // \todo consider other alternatives
      switch((*i).getKind()) {
      case kind::FLOATINGPOINT_ABS :

	clause.clear();
	clause.push_back(CartesianAssignment(*i,TRP::meetIrreducible< TRP::interval< CVC4::FloatingPointLiteral > >(+0.0, false)));
	((ClauseDB &)trans).add(TRP::createDisjunction<AbstractElementWithTrail>(clause));

	break;

      case kind::FLOATINGPOINT_SQRT :

	clause.clear();
	clause.push_back(CartesianAssignment(*i,TRP::meetIrreducible< TRP::interval< CVC4::FloatingPointLiteral > >(-INFINITY, true)));
	((ClauseDB &)trans).add(TRP::createDisjunction<AbstractElementWithTrail>(clause));

	break;

      case kind::FLOATINGPOINT_NEG :
      case kind::FLOATINGPOINT_PLUS :
      case kind::FLOATINGPOINT_MULT :
      case kind::FLOATINGPOINT_DIV :
      case kind::FLOATINGPOINT_FMA :
      case kind::FLOATINGPOINT_REM :
      case kind::FLOATINGPOINT_RTI :
      case kind::FLOATINGPOINT_MIN :
      case kind::FLOATINGPOINT_MAX :
	// No action needed
	break;

      default :
	Unreachable("Unknown operator kind");
      }
    }


    // Relations have to be dispatched in an abstraction specific manner
    // \todo : convert some to clauses, mangle others into the true
    // form until an SMT domain is added
    Trace("fp") << "Adding relations" << std::endl;
    for (NodeSet::const_iterator i = floatingPointRelations.begin();
	 i != floatingPointRelations.end();
	 ++i) {

      Assert(this->d_valuation.isSatLiteral(*i));

      bool value = false;
      bool ret = this->d_valuation.hasSatValue(*i,value);
      Assert(ret == true); // At the given effort level, all relations
			   // should have an assigned SAT value.
      Trace("fp") << *i << " is " << (value ? "true" : "false") << std::endl;

      ((Expressions &)trans).add(TRP::createCVC4Term<AbstractElementWithTrail>(*i,value));
    }


    Trace("fp") << "Running TRP" << std::endl;
    Solver solver;

    switch ( solver.solve(astate, trans) ) {
    case TRP::transformerRefinementResult::Bottom : 
      Trace("fp") << "TRP returns bottom" << std::endl;
      {
	// \todo : return more compact failure clauses to the SAT-solver

	NodeBuilder<> conjunction(kind::AND);

	while(!done()) {
	  // Get all the assertions
	  Assertion assertion = get();
	  conjunction <<  assertion.assertion;	  
	}
		
	Node reason = conjunction;
	this->d_out->conflict(reason);
      }

      break;

    case TRP::transformerRefinementResult::NotBottom :
      Trace("fp") << "TRP returns not-bottom" << std::endl;

      Trace("fp") << astate << std::endl;
      // \todo : model generation

      // This is kind of ugly as we don't work like this at the moment
      // but it is required to signal that the solver has completly
      // processed the input, so ...
      while(!done()) { Assertion assertion = get(); }
      break;

    case TRP::transformerRefinementResult::Unknown : 
      Trace("fp") << "TRP returns unknown" << std::endl;
      Assert("Floating-point decision procedure appears to be incomplete?");
      this->d_out->setIncomplete();
      break;

    default :
      Unreachable("Unknown TRP result");
      break;
    }

  }

  return;

#if 0

  while(!done()) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("fp") << "TheoryFp::check(): processing " << fact << std::endl;

    // Do the work
    switch(fact.getKind()) {

    /* cases for all the theory's kinds go here... */

    default:
      Trace("fp") << "assert" << fact << std::endl;
      //Unhandled(fact.getKind());
    }
  }
#endif

}/* TheoryFp::check() */

}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
