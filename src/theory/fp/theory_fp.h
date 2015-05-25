/*********************                                                        */
/*! \file theory_fp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

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
  /** Equality engine */
  #if FPEQ
  class NotifyClass : public eq::EqualityEngineNotify {
    protected :
      TheoryFp& theorySolver;

    public:
    NotifyClass(TheoryFp& solver): theorySolver(solver) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value);
    bool eqNotifyTriggerPredicate(TNode predicate, bool value);
    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value);
    void eqNotifyConstantTermMerge(TNode t1, TNode t2);
    void eqNotifyNewClass(TNode t) { }
    void eqNotifyPreMerge(TNode t1, TNode t2) { }
    void eqNotifyPostMerge(TNode t1, TNode t2) { }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) { }
  };
  
  NotifyClass notification;
  eq::EqualityEngine equalityEngine;
  #endif

  /** Bit-blasting conversion */
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

  #if FPEQ
  void setMasterEqualityEngine(eq::EqualityEngine* eq);

  void explain(TNode literal, std::vector<TNode> &assumptions);
  #endif

};/* class TheoryFp */

}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__FP__THEORY_FP_H */
