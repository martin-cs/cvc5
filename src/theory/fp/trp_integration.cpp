#include "theory/fp/trp_integration.h"


namespace TRP {

  typedef floatingPointInterval< CVC4::FloatingPointLiteral > fpi;


  /* A helper function to update the domain with the new intervals
   * computed.  It would be nice to do these updates in place but if
   * this is done then the meet() interface is not used and thus the
   * trail and watch lists are not updated.
   */

  transformerResult::s updateInterval (CVC4::theory::fp::AbstractElementWithTrail &astate,
		       const CVC4::Node node,
		       const fpi &oldInterval,
		       const fpi &newInterval) {

    transformerResult::s result = transformerResult::None;

    // Update the NaN proposition
    if (!(oldInterval.getLeft() == newInterval.getLeft())) {

      switch (newInterval.getLeft().isComplete()) {
      case downwardCompleteness::Incomplete :
	/* Do nothing */
	break;

      case downwardCompleteness::Complete :
	{
	  CVC4::theory::fp::CartesianAssignment assgn(node,newInterval.getLeft().getConcreteValue());
	  astate.meet(assgn);
	  result |= transformerResult::Progress;
	}
	break;

      case downwardCompleteness::Bottom :
	{
	  CVC4::theory::fp::CartesianAssignment assgnT(node,true);
	  CVC4::theory::fp::CartesianAssignment assgnF(node,false);

	  astate.meet(assgnT);
	  astate.meet(assgnF);

	  result |= transformerResult::Bottom;
	}
	break;

      default :
	Unreachable("Proposition with unknown status");
	break;
      }
    }


    // Update the interval
    if (oldInterval.getRight().lower < newInterval.getRight().lower) {
      meetIrreducible< interval< CVC4::FloatingPointLiteral > > bound(newInterval.getRight().lower, false);
      
      astate.meet(CVC4::theory::fp::CartesianAssignment(node, bound));
      result |= transformerResult::Progress;
    }

    if (newInterval.getRight().upper < oldInterval.getRight().upper) {
      meetIrreducible< interval< CVC4::FloatingPointLiteral > > bound(newInterval.getRight().upper, true);

      astate.meet(CVC4::theory::fp::CartesianAssignment(node, bound));
      result |= transformerResult::Progress;
    }


    // Pick up if the interval has become conflicting
    if (astate[node].isComplete() == downwardCompleteness::Bottom) {
      result |= transformerResult::Bottom;
    }

    return result;
  }


  template <> 
    transformerResult::s cvc4term<CVC4::theory::fp::AbstractElementWithTrail>::update
    (CVC4::theory::fp::AbstractElementWithTrail &astate,
     cvc4term<CVC4::theory::fp::AbstractElementWithTrail>::WLT &,  // Watch list are not changed
     wlist *activatedList) {
    bool childActivated;
    int activeNode;

    TRACE("cvc4term<interval>") << "update " << this->node;

    if (activatedList == &(this->main)) {
      childActivated = false;
      activeNode = -1;

      Assert(this->childWL + activeNode == &this->main);

    } else {
      memMix base;
      memMix offset;

      base.ptr = &(this->childWL);
      offset.ptr = activatedList;

      childActivated = true;
      activeNode = (offset.n - base.n) / sizeof(wlist);

      Assert((activeNode >= 0) && ((unsigned) activeNode < this->node.getNumChildren()));
    }
    
    TRACE("cvc4term<interval>") << " activated by " << this->node[activeNode] << std::endl;



    /* Forwards propagation (for a and b to a+b) corresponds to
     * propagation 'upwards' in the node tree (from child to parent). */

    switch (this->node.getKind()) {
      /******** Operations ********/
    case CVC4::kind::FLOATINGPOINT_ABS :

      if (childActivated) {
	fpi newMain;
	if (fpi::absForwardPropagate(astate[this->node], astate[this->node[0]], newMain)) {
	  return updateInterval(astate, this->node, astate[this->node], newMain);
	}
      } else {
	fpi newChild;
	if (fpi::absBackwardPropagate(astate[this->node], astate[this->node[0]], newChild)) {
	  return updateInterval(astate, this->node[0], astate[this->node[0]], newChild);
	}
      }
      return transformerResult::None;
      break;

    case CVC4::kind::FLOATINGPOINT_NEG :
      if (childActivated) {
	fpi newMain;
	if (fpi::negForwardPropagate(astate[this->node], astate[this->node[0]], newMain)) {
	  return updateInterval(astate, this->node, astate[this->node], newMain);
	}
      } else {
	fpi newChild;
	if (fpi::negBackwardPropagate(astate[this->node], astate[this->node[0]], newChild)) {
	  return updateInterval(astate, this->node[0], astate[this->node[0]], newChild);
	}
      }
      return transformerResult::None;
      break;


    case CVC4::kind::FLOATINGPOINT_PLUS :
    case CVC4::kind::FLOATINGPOINT_MULT :
    case CVC4::kind::FLOATINGPOINT_DIV :
    case CVC4::kind::FLOATINGPOINT_FMA :
    case CVC4::kind::FLOATINGPOINT_SQRT :
    case CVC4::kind::FLOATINGPOINT_REM :
    case CVC4::kind::FLOATINGPOINT_RTI :
    case CVC4::kind::FLOATINGPOINT_MIN :
    case CVC4::kind::FLOATINGPOINT_MAX :
      Unimplemented("Operation not yet supported");
      break;
      
      /******** Comparisons ********/
    case CVC4::kind::FLOATINGPOINT_LT :
      Assert(childActivated);   // As the actual nodes themselves don't have an abstract value
      {
	fpi newLeft;
	fpi newRight;
	
	if (this->assignment) {
	  if (fpi::ltTruePropagate(astate[this->node[0]], astate[this->node[1]], newLeft, newRight)) {
	    return updateInterval(astate, this->node[0], astate[this->node[0]], newLeft) |
	      updateInterval(astate, this->node[1], astate[this->node[1]], newRight);
	  }
	  
	} else {
	  if (fpi::ltFalsePropagate(astate[this->node[0]], astate[this->node[1]], newLeft, newRight)) {
	    return updateInterval(astate, this->node[0], astate[this->node[0]], newLeft) |
	      updateInterval(astate, this->node[1], astate[this->node[1]], newRight);
	  }
	  
	}
	
	return transformerResult::None;
      }
      break;

    case CVC4::kind::FLOATINGPOINT_LEQ :
      Assert(childActivated);   // As the actual nodes themselves don't have an abstract value
      {
	fpi newLeft;
	fpi newRight;
	
	if (this->assignment) {
	  if (fpi::leqTruePropagate(astate[this->node[0]], astate[this->node[1]], newLeft, newRight)) {
	    return updateInterval(astate, this->node[0], astate[this->node[0]], newLeft) |
	      updateInterval(astate, this->node[1], astate[this->node[1]], newRight);
	  }
	  
	} else {
	  if (fpi::leqFalsePropagate(astate[this->node[0]], astate[this->node[1]], newLeft, newRight)) {
	    return updateInterval(astate, this->node[0], astate[this->node[0]], newLeft) |
	      updateInterval(astate, this->node[1], astate[this->node[1]], newRight);
	  }
	  
	}
	
	return transformerResult::None;
      }
      break;

    case CVC4::kind::EQUAL : 
    case CVC4::kind::FLOATINGPOINT_EQ :
    case CVC4::kind::FLOATINGPOINT_ISN :
    case CVC4::kind::FLOATINGPOINT_ISSN :
    case CVC4::kind::FLOATINGPOINT_ISZ :
    case CVC4::kind::FLOATINGPOINT_ISINF :
    case CVC4::kind::FLOATINGPOINT_ISNAN :
      Assert(childActivated);   // As the actual nodes themselves are not currently tracked
      Unimplemented("Logical operator not yet supported");
      break;
      
      /******** Conversions ********/
    case CVC4::kind::FLOATINGPOINT_FP :
    case CVC4::kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR :
    case CVC4::kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT : 
    case CVC4::kind::FLOATINGPOINT_TO_FP_REAL : 
    case CVC4::kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR :
    case CVC4::kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR :
      Unimplemented("Conversions to floating-point from non-literal values not supported.");
      break;
      
    case CVC4::kind::FLOATINGPOINT_TO_UBV : 
    case CVC4::kind::FLOATINGPOINT_TO_SBV : 
    case CVC4::kind::FLOATINGPOINT_TO_REAL :
      Unimplemented("Conversions from non-literal floating-point values not supported.");
    break;


    /******** Constants ********/
    case CVC4::kind::CONST_FLOATINGPOINT :
    case CVC4::kind::CONST_ROUNDINGMODE :
      
    /******** Variables ********/
    case CVC4::kind::VARIABLE :
    case CVC4::kind::BOUND_VARIABLE :
      Unreachable("Kind should not be registered as an operation.");
      break;


    case CVC4::kind::FLOATINGPOINT_SUB :
    case CVC4::kind::FLOATINGPOINT_GEQ :
    case CVC4::kind::FLOATINGPOINT_GT :
      Unreachable("Kind should have been removed by rewriter.");
      break;


    /******** Types ********/      
    case CVC4::kind::FLOATINGPOINT_TYPE : 
      Unreachable("Floating-point type when operation expected?");
      break;

    default :
      Unhandled(node.getKind());
      break;
    }


    Unreachable("Fall through handling of floating-point interval cvc4term::update()");
    return transformerResult::None;
  }
}
