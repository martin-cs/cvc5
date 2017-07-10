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
#include "theory/theory_model.h"

#include <stack>

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

namespace helper {
  Node buildConjunct(const std::vector<TNode> &assumptions) {
    if (assumptions.size() == 0) {
      return NodeManager::currentNM()->mkConst<bool>(true);

    } else if (assumptions.size() == 1) {
      return assumptions[0];

    } else {
      // \todo see bv::utils::flattenAnd

      NodeBuilder<> conjunction(kind::AND);
      for (std::vector<TNode>::const_iterator it = assumptions.begin();
	   it != assumptions.end();
	   ++it) {
	conjunction << *it;
      }

      return conjunction;
    }
  }
}


/** Constructs a new instance of TheoryFp w.r.t. the provided contexts. */
TheoryFp::TheoryFp(context::Context* c,
		   context::UserContext* u,
		   OutputChannel& out,
		   Valuation valuation,
		   const LogicInfo& logicInfo) :
  Theory(THEORY_FP, c, u, out, valuation, logicInfo),
  notification(*this),
  equalityEngine(notification, c, "theory::fp::TheoryFp", true),
  conv(u),
  expansionRequested(false),
  conflict(c, false),
  conflictNode(c, Node::null())
  {

    // Kinds that are to be handled in the congruence closure
    
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ABS);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_NEG);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_PLUS);
    //equalityEngine.addFunctionKind(kind::FLOATINGPOINT_SUB); // Removed
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_MULT);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_DIV);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_FMA);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_SQRT);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_REM);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_RTI);
    // equalityEngine.addFunctionKind(kind::FLOATINGPOINT_MIN); // Care needed w.r.t. +/-0
    // equalityEngine.addFunctionKind(kind::FLOATINGPOINT_MAX);

    // equalityEngine.addFunctionKind(kind::FLOATINGPOINT_EQ); // Removed
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_LEQ);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_LT);
    // equalityEngine.addFunctionKind(kind::FLOATINGPOINT_GEQ); // Removed
    // equalityEngine.addFunctionKind(kind::FLOATINGPOINT_GT); // Removed
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ISN);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ISSN);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ISZ);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ISINF);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ISNAN);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ISNEG);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ISPOS);

    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR_OP);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_REAL_OP);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP);
    // equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_GENERIC_OP); // Needed in parsing, should be rewritten away

    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_UBV_OP);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_SBV_OP);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_REAL);

    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_NAN);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_INF);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_ZERO);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_SIGN);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_EXPONENT);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND);
    equalityEngine.addFunctionKind(kind::ROUNDINGMODE_BITBLAST);


}/* TheoryFp::TheoryFp() */



Node TheoryFp::expandDefinition(LogicRequest &lr, Node node) {
  Trace("fp-expandDefinition") << "TheoryFp::expandDefinition(): " << node << std::endl;

  if (!this->expansionRequested) {
    lr.widenLogic(THEORY_UF); // Needed for conversions to/from real
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

#ifdef SYMFPUPROPISBOOL    
    d_out->lemma(addA, false, true);
#else
    NodeManager *nm = NodeManager::currentNM();

    d_out->lemma(nm->mkNode(kind::EQUAL,
			    addA,
			    nm->mkConst(::CVC4::BitVector(1U, 1U))),
		 false,
		 true);
#endif

    ++oldAdditionalAssertions;
  }



  // Equate the floating-point atom and the converted one.
  // Also adds the bit-vectors to the bit-vector solver.
  if (node.getType().isBoolean()) {
    if (converted != node) {
      Assert(converted.getType().isBitVector());

      NodeManager *nm = NodeManager::currentNM();

#ifdef SYMFPUPROPISBOOL
      d_out->lemma(nm->mkNode(kind::EQUAL, node, converted),
		   false,
		   true);
#else
      d_out->lemma(nm->mkNode(kind::EQUAL,
			      node,
			      nm->mkNode(kind::EQUAL,
					 converted,
					 nm->mkConst(::CVC4::BitVector(1U, 1U)))),
		   false,
		   true);
#endif

    } else {
      // Component bits should not be altered.
      // These are the only bits that should be allowed through
      Assert((node.getKind() == kind::FLOATINGPOINT_COMPONENT_NAN) ||
	     (node.getKind() == kind::FLOATINGPOINT_COMPONENT_INF) ||
	     (node.getKind() == kind::FLOATINGPOINT_COMPONENT_ZERO) ||
	     (node.getKind() == kind::FLOATINGPOINT_COMPONENT_SIGN) ||
	     (node.getKind() == kind::EQUAL));
    }
  }

  return;
}

void TheoryFp::preRegisterTerm(TNode node) {
  Trace("fp-preRegisterTerm") << "TheoryFp::preRegisterTerm(): " << node << std::endl;

  // Add to the equality engine
  if (node.getKind() == kind::EQUAL) {
    equalityEngine.addTriggerEquality(node);
  } else {
    equalityEngine.addTerm(node);
  }

  convertAndEquateTerm(node);
  return;
}

void TheoryFp::addSharedTerm(TNode node) {
  Trace("fp-addSharedTerm") << "TheoryFp::addSharedTerm(): " << node << std::endl;

  // Add to the equality engine
  if (node.getKind() == kind::EQUAL) {
    equalityEngine.addTriggerEquality(node);
  } else {
    equalityEngine.addTerm(node);
  }

  convertAndEquateTerm(node);
  return;
}

bool TheoryFp::handlePropagation(TNode node) {
  Trace("fp") << "TheoryFp::handlePropagation(): propagate " << node << std::endl;

  bool stat = d_out->propagate(node);

  if (!stat)
    handleConflict(node);

  return stat;
}


void TheoryFp::handleConflict(TNode node) {
  Trace("fp") << "TheoryFp::handleConflict(): conflict detected " << node << std::endl;

  conflictNode = node;
  conflict = true;
  d_out->conflict(node);
  return;
}
  

void TheoryFp::check(Effort level) {

  while(!done() && !conflict) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("fp") << "TheoryFp::check(): processing " << fact << std::endl;

    // Only handle equalities; the rest should be handled by
    // the bit-vector theory

    bool negated = fact.getKind() == kind::NOT;
    TNode predicate = negated ? fact[0] : fact;

    if (predicate.getKind() == kind::EQUAL) {
      if (negated) {
	Debug("fp-eq") << "TheoryFp::check(): adding dis-equality " << fact[0] << std::endl;
	equalityEngine.assertEquality(predicate, false, fact);
	
      } else {
	Debug("fp-eq") << "TheoryFp::check(): adding equality " << fact << std::endl;
	equalityEngine.assertEquality(predicate, true, fact);
      }
    } else {
      if (equalityEngine.isFunctionKind(predicate.getKind())) {
	Debug("fp-eq") << "TheoryFp::check(): adding predicate " << predicate << " is " << !negated << std::endl;
	equalityEngine.assertPredicate(predicate, !negated, fact);
      }
    }


  }

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


void TheoryFp::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  equalityEngine.setMasterEqualityEngine(eq);
}

Node TheoryFp::explain(TNode n) {
  Trace("fp") << "TheoryFp::explain(): explain " << n << std::endl;
  
  // All things we assert directly (and not via bit-vector) should 
  // come from the equality engine so this should be sufficient...
  std::vector<TNode> assumptions;
  
  bool polarity = n.getKind() != kind::NOT;
  TNode atom = polarity ? n : n[0];
  if (atom.getKind() == kind::EQUAL) {
    equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  } else {
    equalityEngine.explainPredicate(atom, polarity, assumptions);
  }

  return helper::buildConjunct(assumptions);
}




  Node TheoryFp::getModelValue(TNode var) {
    return conv.getValue(d_valuation, var);
  }

  void TheoryFp::collectModelInfo(TheoryModel *m, bool fullModel) {
    std::set<Node> relevantTerms;

    // Work out which variables are needed
    computeRelevantTerms(relevantTerms);

    if (Trace.isOn("fp-collectModelInfo")) {
      for (std::set<Node>::const_iterator i(relevantTerms.begin());
	   i != relevantTerms.end();
	   ++i) {
	Trace("fp-collectModelInfo") << "TheoryFp::collectModelInfo(): relevantTerms " << *i << std::endl;
      }
    }


    std::hash_set<TNode, TNodeHashFunction> visited;
    std::stack<TNode> working;
    std::set<TNode> relevantVariables;
    for (std::set<Node>::const_iterator i(relevantTerms.begin());
	 i != relevantTerms.end();
	 ++i) {
      working.push(*i);
    }

    while (!working.empty()) {
      TNode current = working.top();
      working.pop();

      // Ignore things that have already been explored
      if (visited.find(current) == visited.end()) {
	visited.insert(current);

	TypeNode t(current.getType());

	if ((t.isRoundingMode() ||
	     t.isFloatingPoint()) &&
	    this->isLeaf(current)) {
	  relevantVariables.insert(current);
	}

	for (size_t i = 0; i < current.getNumChildren(); ++i) {
	  working.push(current[i]);
	}
      }

    }



    for (std::set<TNode>::const_iterator i(relevantVariables.begin());
	 i != relevantVariables.end();
	 ++i) {
      TNode node = *i;

      Trace("fp-collectModelInfo") << "TheoryFp::collectModelInfo(): relevantVariable " << node << std::endl;
      
      m->assertEquality(node,
			conv.getValue(d_valuation, node),
			true);
    }

    return;
  }


  bool TheoryFp::NotifyClass::eqNotifyTriggerEquality(TNode equality, bool value) {
    Debug("fp-eq") << "TheoryFp::eqNotifyTriggerEquality(): call back as equality" << equality << " is " << value << std::endl;

    if (value) {
      return theorySolver.handlePropagation(equality);
    } else {
      return theorySolver.handlePropagation(equality.notNode());
    }
  }

  bool TheoryFp::NotifyClass::eqNotifyTriggerPredicate(TNode predicate, bool value) {
    Debug("fp-eq") << "TheoryFp::eqNotifyTriggerPredicate(): call back as predicate" << predicate << " is " << value << std::endl;

    if (value) {
      return theorySolver.handlePropagation(predicate);
    } else {
      return theorySolver.handlePropagation(predicate.notNode());
    }
  }

  bool TheoryFp::NotifyClass::eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) {
    Debug("fp-eq") << "TheoryFp::eqNotifyTriggerTermEquality(): call back as " << t1 << (value ? " = " : " != ") << t2 << std::endl;

    if (value) {
      return theorySolver.handlePropagation(t1.eqNode(t2));
    } else {
      return theorySolver.handlePropagation(t1.eqNode(t2).notNode());
    }
  }

  void TheoryFp::NotifyClass::eqNotifyConstantTermMerge(TNode t1, TNode t2) {
    Debug("fp-eq") << "TheoryFp::eqNotifyConstantTermMerge(): call back as " << t1 << " = " << t2 << std::endl;

    std::vector<TNode> assumptions;
    theorySolver.equalityEngine.explainEquality(t1, t2, true, assumptions);

    Node conflict = helper::buildConjunct(assumptions);

    theorySolver.handleConflict(conflict);
  }


}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
