#include "cvc4_private.h"

#ifndef __CVC4__THEORY__FP__THEORY_FP_H
#define __CVC4__THEORY__FP__THEORY_FP_H

#include "theory/theory.h"

#include "theory/fp/fp_converter.h"


namespace CVC4 {
namespace theory {
namespace fp {

class TheoryFp : public Theory {
protected :
  fpConverter conv;
  bool expansionRequested;

  void convertAndEquateTerm(TNode node);

public:

  /** Constructs a new instance of TheoryFp w.r.t. the provided contexts. */
  TheoryFp(context::Context* c,
               context::UserContext* u,
               OutputChannel& out,
               Valuation valuation,
               const LogicInfo& logicInfo);

  Node expandDefinition(LogicRequest &lr, Node node);

  void preRegisterTerm(TNode node);
  void addSharedTerm(TNode node);

  void check(Effort);

  Node getModelValue(TNode var);
  void collectModelInfo(TheoryModel *m, bool fullModel);

  std::string identify() const {
    return "THEORY_FP";
  }

};/* class TheoryFp */

}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__FP__THEORY_FP_H */
