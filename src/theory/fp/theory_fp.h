#include "cvc4_private.h"

#ifndef __CVC4__THEORY__FP__THEORY_FP_H
#define __CVC4__THEORY__FP__THEORY_FP_H

#include "theory/theory.h"

#include "context/cdhashset.h"


namespace CVC4 {
namespace theory {
namespace fp {

class TheoryFp : public Theory {
  protected :
    typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

    /** Sets of the constants used */
    NodeSet floatingPointConstants;
    NodeSet roundingModeConstants;

    /** Nodes used and their position in the product */
    NodeSet floatingPointVariables;
    NodeSet floatingPointOperations;
    NodeSet floatingPointConversions;

    /** Predicates that link from floating point terms to logical formulae */
    NodeSet floatingPointRelations;

public:

  /** Constructs a new instance of TheoryFp w.r.t. the provided contexts. */
  TheoryFp(context::Context* c,
               context::UserContext* u,
               OutputChannel& out,
               Valuation valuation,
               const LogicInfo& logicInfo,
               QuantifiersEngine* qe);

  void preRegisterTerm(TNode);
  void check(Effort);

  std::string identify() const {
    return "THEORY_FP";
  }

};/* class TheoryFp */

}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__FP__THEORY_FP_H */
