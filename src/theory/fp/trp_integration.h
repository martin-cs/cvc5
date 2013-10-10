


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



  typedef TRP::firstUnassigned< FloatingPointInterval, TRP::typePair<TRP::split<TRP::proposition>, TRP::split<TRP::interval< CVC4::FloatingPointLiteral > > > >  NANFirstThenSplit;
  typedef TRP::firstUnassigned< AbstractElement, NANFirstThenSplit > Heuristic;

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

