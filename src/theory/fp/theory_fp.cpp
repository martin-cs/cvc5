/*********************                                                        */
/*! \file theory_fp.cpp
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

#include "theory/fp/theory_fp.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace fp {

namespace removeToFPGeneric {

  Node removeToFPGeneric (TNode node) {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_GENERIC);

    FloatingPointToFPGeneric info =
        node.getOperator().getConst<FloatingPointToFPGeneric>();

    size_t children = node.getNumChildren();

    Node op;

    if (children == 1) {
      op = NodeManager::currentNM()->mkConst(
          FloatingPointToFPIEEEBitVector(info.t.exponent(),
                                         info.t.significand()));
      return NodeManager::currentNM()->mkNode(op, node[0]);

    } else {
      Assert(children == 2);
      Assert(node[0].getType().isRoundingMode());

      TypeNode t = node[1].getType();

      if (t.isFloatingPoint()) {
	op = NodeManager::currentNM()->mkConst(
            FloatingPointToFPFloatingPoint(info.t.exponent(),
                                           info.t.significand()));
      } else if (t.isReal()) {
	op = NodeManager::currentNM()->mkConst(
            FloatingPointToFPReal(info.t.exponent(),
                                  info.t.significand()));
      } else if (t.isBitVector()) {
	op = NodeManager::currentNM()->mkConst(
            FloatingPointToFPSignedBitVector(info.t.exponent(),
                                             info.t.significand()));

      } else {
	throw TypeCheckingExceptionPrivate(
            node,
            "cannot rewrite to_fp generic due to incorrect type of second "
            "argument");
      }

      return NodeManager::currentNM()->mkNode(op, node[0], node[1]);
    }

    Unreachable("to_fp generic not rewritten");
  }
}


/** Constructs a new instance of TheoryFp w.r.t. the provided contexts. */
TheoryFp::TheoryFp(context::Context* c, context::UserContext* u,
                   OutputChannel& out, Valuation valuation,
                   const LogicInfo& logicInfo)
    : Theory(THEORY_FP, c, u, out, valuation, logicInfo),
      conv(u),
      expansionRequested(false)
{}/* TheoryFp::TheoryFp() */


Node TheoryFp::expandDefinition(LogicRequest &lr, Node node) {
  Trace("fp-expandDefinition") << "TheoryFp::expandDefinition(): " << node << std::endl;

  if (!this->expansionRequested) {
    lr.widenLogic(THEORY_UF);
    lr.widenLogic(THEORY_BV);
    this->expansionRequested = true;
  }

  if (node.getKind() == kind::FLOATINGPOINT_TO_FP_GENERIC) {
    Node res(removeToFPGeneric::removeToFPGeneric(node));

    Trace("fp-expandDefinition") << "TheoryFp::expandDefinition(): TO_FP_GENERIC rewritten to " << res << std::endl;

    return res;
  } else {
    return node;
  }
}

void TheoryFp::convertAndEquateTerm(TNode node) {
  Trace("fp-convertTerm") << "TheoryFp::convertTerm(): " << node << std::endl;
  size_t oldAdditionalAssertions = conv.additionalAssertions.size();

  Node converted(conv.convert(node));

  if (converted != node) {
    Debug("fp-convertTerm") << "TheoryFp::convertTerm(): before " << node << std::endl;
    Debug("fp-convertTerm") << "TheoryFp::convertTerm(): after  " << converted << std::endl;
  }

  size_t newAdditionalAssertions = conv.additionalAssertions.size();
  Assert(oldAdditionalAssertions <= newAdditionalAssertions);

  while (oldAdditionalAssertions < newAdditionalAssertions) {
    Node addA = conv.additionalAssertions[oldAdditionalAssertions];

    Debug("fp-convertTerm") << "TheoryFp::convertTerm(): additional assertion  " << addA << std::endl;
    
    d_out->lemma(addA, false, true);

    ++oldAdditionalAssertions;
  }


  // Equate the floating-point atom and the converted one
  // Also adds the bit-vectors to the bit-vector solver
  if (node.getType().isBoolean()) {
    Assert(converted != node);

    d_out->lemma(NodeManager::currentNM()->mkNode(kind::IFF, node, converted),
		 false,
		 true);
  }

  return;
}

void TheoryFp::preRegisterTerm(TNode node) {
  Trace("fp-preRegisterTerm") << "TheoryFp::preRegisterTerm(): " << node << std::endl;

  convertAndEquateTerm(node);
  return;
}

void TheoryFp::addSharedTerm(TNode node) {
  Trace("fp-addSharedTerm") << "TheoryFp::addSharedTerm(): " << node << std::endl;

  convertAndEquateTerm(node);
  return;
}



void TheoryFp::check(Effort level) {

  /* Checking should be handled by the bit-vector engine */
  return;

#if 0
  if (done() && !fullEffort(level)) {
    return;
  }

  while(!done()) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("fp") << "TheoryFp::check(): processing " << fact << std::endl;

    // Do the work
    switch(fact.getKind()) {

    /* cases for all the theory's kinds go here... */

    default:
      Unhandled(fact.getKind());
    }
  }
#endif

}/* TheoryFp::check() */


  Node TheoryFp::getModelValue(TNode var) {
    return conv.getValue(d_valuation, var);
  }


}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
