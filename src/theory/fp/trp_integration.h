// If this is included first, TRP will use the CVC4 tracing and debugging
#include "util/output.h"


#include "trp/abstractions/floatingPointInterval.h"
#include "trp/abstractions/cartesian.h"
#include "trp/abstractions/trail.h"

#include "trp/transformers/disjunction.h"
#include "trp/transformers/set.h"
#include "trp/transformers/watches.h"
#include "trp/transformers/watches-cartesian.h"
#include "trp/transformers/cvc4term.h"
#include "trp/transformers/meet.h"

#include "trp/heuristics/firstUnassigned.h"
#include "trp/heuristics/split.h"

#include "trp/algorithms/transformerRefinement.h"
#include "trp/algorithms/probeDecisionLearning.h"



namespace CVC4 {
namespace theory {
namespace fp {

  
  // Helper classes
  template <class Key, class Data>
    class TRPCartesianStore;
  
  template <class Data>
    class TRPCartesianStore<CVC4::Node, Data> : public std::hash_map<CVC4::Node, Data, CVC4::NodeHashFunction> {};
  
  
  
  /*** TRP typedefs ***/
  typedef TRP::floatingPointInterval< CVC4::FloatingPointLiteral > FloatingPointInterval;
  typedef TRP::meetIrreducible< FloatingPointInterval > isNANOrHalfSpace;
  
  typedef TRP::cartesian< CVC4::Node, FloatingPointInterval, TRPCartesianStore> AbstractElement;
  typedef TRP::meetIrreducible< AbstractElement > CartesianAssignment;
  
  typedef TRP::trail< AbstractElement > AbstractElementWithTrail;
  typedef TRP::meetIrreducible< AbstractElementWithTrail > Assignment;
  
  

  typedef TRP::disjunction< AbstractElementWithTrail > LearntClause;
  typedef TRP::set< AbstractElementWithTrail, TRP::disjunction> ClauseDB;

  typedef TRP::cvc4term<AbstractElementWithTrail> NodeReasoner;
  typedef TRP::set<AbstractElementWithTrail, TRP::cvc4term> Expressions;

  typedef TRP::meet<AbstractElementWithTrail, ClauseDB, Expressions> Transformer;

}
}
}


namespace TRP {
  template <class H>
    struct largestUnassignedVariableFirst {
      
    protected :
      H base;
      typedef CVC4::theory::fp::AbstractElement SAbs;
      typedef CVC4::FloatingPointLiteral Number;

      void scoreInterval(const interval< Number > &i, Number &score) {
	ARGUMENTERROR(i.isComplete() == downwardCompleteness::Incomplete);

	Number low(i.lower);
	if (low.isInfinite()) {
	  DYNAMICASSERT(low == Number(-INFINITY));  // As incomplete
	  low.inc();
	}

	score = i.upper;
	if (score.isInfinite()) {
	  DYNAMICASSERT(score == Number(+INFINITY));  // As incomplete
	  score.dec();
	}

	Number half(0.5);
	low.mul(FE_TONEAREST,half);
	score.mul(FE_TONEAREST,half);

	score.sub(FE_TONEAREST,low);

	return;
      }


    public :
      meetIrreducible<SAbs> extrapolate (const SAbs &astate) {
 
	downwardCompleteness result(downwardCompleteness::Unknown);
	bool uninitialised = true;
	SAbs::keyType currentLargest;
	Number current;
	Number candidate;

	TRACE("largestUnassignedVariableFirst") << "extrapolate" << std::endl;
	DYNAMICASSERT(astate.isComplete() == downwardCompleteness::Incomplete);

	for (SAbs::constAbsIterator i = astate.begin(); i != astate.end(); ++i) {
	  unsigned k = (*i).first.getKind();

	  if (((k == CVC4::kind::VARIABLE) ||
	       (k == CVC4::kind::BOUND_VARIABLE)) &&
	      ((*i).second.isComplete() == downwardCompleteness::Incomplete)) {

	    if (((const proposition &)((*i).second)).isComplete() == downwardCompleteness::Incomplete) {
		// Can be set to NaN, thus finish the search
	      currentLargest = (*i).first;
	      uninitialised = false;
	      break;
	    }


	    if (uninitialised) {
	      uninitialised = false;
	      currentLargest = (*i).first;
	      scoreInterval((*i).second, current);

	    } else {
	      scoreInterval((*i).second, candidate);
	      if (candidate > current) {
		currentLargest = (*i).first;
		current.swap(candidate);
	      }
	    }
	  }

	}

	DYNAMICASSERT(uninitialised == false);
	
	return meetIrreducible<SAbs>(currentLargest,
				     base.extrapolate(astate[currentLargest]));
 
      }
    };
}


namespace CVC4 {
namespace theory {
namespace fp {


  typedef TRP::firstUnassigned< FloatingPointInterval, TRP::typePair<TRP::split<TRP::proposition>, TRP::split<TRP::interval< CVC4::FloatingPointLiteral > > > >  NANFirstThenSplit;
  
  // Old branching heuristic
  typedef TRP::firstUnassigned< AbstractElement, NANFirstThenSplit > Heuristic;

  // New branching heuristic
  //typedef TRP::largestUnassignedVariableFirst< NANFirstThenSplit > Heuristic;

  typedef TRP::probeDecisionLearning<AbstractElementWithTrail, Transformer, Heuristic> Solver;

}
}
}

// Specialise the dispatch mechanism
namespace TRP {

  template <> 
    transformerResult::s cvc4term<CVC4::theory::fp::AbstractElementWithTrail>::update
    (CVC4::theory::fp::AbstractElementWithTrail &astate,
     cvc4term<CVC4::theory::fp::AbstractElementWithTrail>::WLT &,  // Watch list are not changed
     wlist *activatedList);

}

