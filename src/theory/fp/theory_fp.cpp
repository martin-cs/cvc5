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
#include "theory/rewriter.h"

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
    NodeManager *nm = NodeManager::currentNM();

    if (children == 1) {
      op = nm->mkConst(FloatingPointToFPIEEEBitVector(info));
      return nm->mkNode(op, node[0]);

    } else {
      Assert(children == 2);
      Assert(node[0].getType().isRoundingMode());

      TypeNode t = node[1].getType();

      if (t.isFloatingPoint()) {
	op = nm->mkConst(FloatingPointToFPFloatingPoint(info));
      } else if (t.isReal()) {
	op = nm->mkConst(FloatingPointToFPReal(info));
      } else if (t.isBitVector()) {
	op = nm->mkConst(FloatingPointToFPSignedBitVector(info));
      } else {
	throw TypeCheckingExceptionPrivate(
            node,
            "cannot rewrite to_fp generic due to incorrect type of second "
            "argument");
      }

      return nm->mkNode(op, node[0], node[1]);
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
  registeredTerms(u),
  conv(u),
  expansionRequested(false),
  conflict(c, false),
  conflictNode(c, Node::null()),
  minMap(u),
  maxMap(u),
  toUBVMap(u),
  toSBVMap(u),
  toRealMap(u),
  realToFloatMap(u),
  floatToRealMap(u),
  abstractionMap(u)
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
    //equalityEngine.addFunctionKind(kind::FLOATINGPOINT_MIN); // Removed
    //equalityEngine.addFunctionKind(kind::FLOATINGPOINT_MAX); // Removed
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_MIN_TOTAL);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_MAX_TOTAL);

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

    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_REAL);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR);
    // equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_GENERIC); // Needed in parsing, should be rewritten away

    //equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_UBV); // Removed
    //equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_SBV); // Removed
    //equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_REAL); // Removed
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_UBV_TOTAL);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_SBV_TOTAL);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_REAL_TOTAL);

    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_NAN);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_INF);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_ZERO);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_SIGN);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_EXPONENT);
    equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND);
    equalityEngine.addFunctionKind(kind::ROUNDINGMODE_BITBLAST);


}/* TheoryFp::TheoryFp() */


Node TheoryFp::minUF (Node node) {
  Assert(node.getKind() == kind::FLOATINGPOINT_MIN);
  TypeNode t(node.getType());
  Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

  NodeManager *nm = NodeManager::currentNM();
  comparisonUFMap::const_iterator i(minMap.find(t));

  Node fun;
  if (i == minMap.end()) {
    std::vector<TypeNode> args(2);
    args[0] = t;
    args[1] = t;
    fun = nm->mkSkolem("floatingpoint_min_zero_case",
		       nm->mkFunctionType(args,
#ifdef SYMFPUPROPISBOOL
					  nm->booleanType()
#else
					  nm->mkBitVectorType(1U)
#endif
					  ),
		       "floatingpoint_min_zero_case",
		       NodeManager::SKOLEM_EXACT_NAME);
    minMap.insert(t,fun);
  } else {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF, fun, node[1], node[0]);  // Application reverses the order or arguments
}


Node TheoryFp::maxUF (Node node) {
  Assert(node.getKind() == kind::FLOATINGPOINT_MAX);
  TypeNode t(node.getType());
  Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

  NodeManager *nm = NodeManager::currentNM();
  comparisonUFMap::const_iterator i(maxMap.find(t));

  Node fun;
  if (i == maxMap.end()) {
    std::vector<TypeNode> args(2);
    args[0] = t;
    args[1] = t;
    fun = nm->mkSkolem("floatingpoint_max_zero_case",
		       nm->mkFunctionType(args,
#ifdef SYMFPUPROPISBOOL
					  nm->booleanType()
#else
					  nm->mkBitVectorType(1U)
#endif
					  ),
		       "floatingpoint_max_zero_case",
		       NodeManager::SKOLEM_EXACT_NAME);
    maxMap.insert(t,fun);
  } else {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF, fun, node[1], node[0]);
}

Node TheoryFp::toUBVUF (Node node) {
  Assert(node.getKind() == kind::FLOATINGPOINT_TO_UBV);

  TypeNode target(node.getType());
  Assert(target.getKind() == kind::BITVECTOR_TYPE);

  TypeNode source(node[1].getType());
  Assert(source.getKind() == kind::FLOATINGPOINT_TYPE);

  std::pair<TypeNode, TypeNode> p(source, target);
  NodeManager *nm = NodeManager::currentNM();
  conversionUFMap::const_iterator i(toUBVMap.find(p));

  Node fun;
  if (i == toUBVMap.end()) {
    std::vector<TypeNode> args(2);
    args[0] = nm->roundingModeType();
    args[1] = source;
    fun = nm->mkSkolem("floatingpoint_to_ubv_out_of_range_case",
		       nm->mkFunctionType(args, target),
		       "floatingpoint_to_ubv_out_of_range_case",
		       NodeManager::SKOLEM_EXACT_NAME);
    toUBVMap.insert(p,fun);
  } else {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF, fun, node[0], node[1]);
}

Node TheoryFp::toSBVUF (Node node) {
  Assert(node.getKind() == kind::FLOATINGPOINT_TO_SBV);

  TypeNode target(node.getType());
  Assert(target.getKind() == kind::BITVECTOR_TYPE);

  TypeNode source(node[1].getType());
  Assert(source.getKind() == kind::FLOATINGPOINT_TYPE);

  std::pair<TypeNode, TypeNode> p(source, target);
  NodeManager *nm = NodeManager::currentNM();
  conversionUFMap::const_iterator i(toSBVMap.find(p));

  Node fun;
  if (i == toSBVMap.end()) {
    std::vector<TypeNode> args(2);
    args[0] = nm->roundingModeType();
    args[1] = source;
    fun = nm->mkSkolem("floatingpoint_to_sbv_out_of_range_case",
		       nm->mkFunctionType(args, target),
		       "floatingpoint_to_sbv_out_of_range_case",
		       NodeManager::SKOLEM_EXACT_NAME);
    toSBVMap.insert(p,fun);
  } else {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF, fun, node[0], node[1]);
}

Node TheoryFp::toRealUF (Node node) {
  Assert(node.getKind() == kind::FLOATINGPOINT_TO_REAL);
  TypeNode t(node[0].getType());
  Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

  NodeManager *nm = NodeManager::currentNM();
  comparisonUFMap::const_iterator i(toRealMap.find(t));

  Node fun;
  if (i == toRealMap.end()) {
    std::vector<TypeNode> args(1);
    args[0] = t;
    fun = nm->mkSkolem("floatingpoint_to_real_infinity_and_NaN_case",
		       nm->mkFunctionType(t, nm->realType()),
		       "floatingpoint_to_real_infinity_and_NaN_case",
		       NodeManager::SKOLEM_EXACT_NAME);
    toRealMap.insert(t,fun);
  } else {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF, fun, node[0]);
}


Node TheoryFp::abstractRealToFloat (Node node) {
  Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_REAL);
  TypeNode t(node.getType());
  Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

  NodeManager *nm = NodeManager::currentNM();
  comparisonUFMap::const_iterator i(floatToRealMap.find(t));

  Node fun;
  if (i == floatToRealMap.end()) {
    std::vector<TypeNode> args(2);
    args[0] = node[0].getType();
    args[1] = node[1].getType();
    fun = nm->mkSkolem("floatingpoint_abstract_real_to_float",
		       nm->mkFunctionType(args, node.getType()),
		       "floatingpoint_abstract_real_to_float",
		       NodeManager::SKOLEM_EXACT_NAME);
    toRealMap.insert(t,fun);
  } else {
    fun = (*i).second;
  }
  Node uf = nm->mkNode(kind::APPLY_UF, fun, node[0], node[1]);

  abstractionMap.insert(uf, node);

  return uf;
}

Node TheoryFp::abstractFloatToReal (Node node) {
  Assert(node.getKind() == kind::FLOATINGPOINT_TO_REAL_TOTAL);
  TypeNode t(node[0].getType());
  Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

  NodeManager *nm = NodeManager::currentNM();
  comparisonUFMap::const_iterator i(floatToRealMap.find(t));

  Node fun;
  if (i == floatToRealMap.end()) {
    std::vector<TypeNode> args(2);
    args[0] = t;
    args[1] = nm->realType();
    fun = nm->mkSkolem("floatingpoint_abstract_float_to_real",
		       nm->mkFunctionType(args, nm->realType()),
		       "floatingpoint_abstract_float_to_real",
		       NodeManager::SKOLEM_EXACT_NAME);
    toRealMap.insert(t,fun);
  } else {
    fun = (*i).second;
  }
  Node uf = nm->mkNode(kind::APPLY_UF, fun, node[0], node[1]);

  abstractionMap.insert(uf, node);

  return uf;
}


void TheoryFp::enableUF(LogicRequest &lr) {
  if (!this->expansionRequested) {
    lr.widenLogic(THEORY_UF); // Needed for conversions to/from real and min/max
    //lr.widenLogic(THEORY_BV); // This has to be done when the logic is set
    this->expansionRequested = true;
  }
  return;
}


Node TheoryFp::expandDefinition(LogicRequest &lr, Node node) {
  Trace("fp-expandDefinition") << "TheoryFp::expandDefinition(): " << node << std::endl;

  Node res = node;

  if (node.getKind() == kind::FLOATINGPOINT_TO_FP_GENERIC) {
    res = removeToFPGeneric::removeToFPGeneric(node);

  } else if (node.getKind() == kind::FLOATINGPOINT_MIN) {
    enableUF(lr);
    res = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_MIN_TOTAL,
					   node[0], node[1], minUF(node));

  } else if (node.getKind() == kind::FLOATINGPOINT_MAX) {
    enableUF(lr);
    res = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_MAX_TOTAL,
					   node[0], node[1], maxUF(node));

  } else if (node.getKind() == kind::FLOATINGPOINT_TO_UBV) {
    enableUF(lr);
    FloatingPointToUBV info = node.getOperator().getConst<FloatingPointToUBV>();
    FloatingPointToUBVTotal newInfo(info);

    res = NodeManager::currentNM()->mkNode(//kind::FLOATINGPOINT_TO_UBV_TOTAL,
					   NodeManager::currentNM()->mkConst(newInfo),
					   node[0], node[1], toUBVUF(node));

  } else if (node.getKind() == kind::FLOATINGPOINT_TO_SBV) {
    enableUF(lr);
    FloatingPointToSBV info = node.getOperator().getConst<FloatingPointToSBV>();
    FloatingPointToSBVTotal newInfo(info);

    res = NodeManager::currentNM()->mkNode(//kind::FLOATINGPOINT_TO_SBV_TOTAL,
					   NodeManager::currentNM()->mkConst(newInfo),
					   node[0], node[1], toSBVUF(node));

  } else if (node.getKind() == kind::FLOATINGPOINT_TO_REAL) {
    enableUF(lr);
    res = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_TO_REAL_TOTAL,
					   node[0], toRealUF(node));

  } else {
    // Do nothing
  }

  // We will need to enable UF to abstract these in ppRewrite
  if (res.getKind() == kind::FLOATINGPOINT_TO_REAL_TOTAL ||
      res.getKind() == kind::FLOATINGPOINT_TO_FP_REAL) {
    enableUF(lr);
  }

  if (res != node) {
    Trace("fp-expandDefinition") << "TheoryFp::expandDefinition(): " << node << " rewritten to " << res << std::endl;
  }

  return res;
}

  
Node TheoryFp::ppRewrite(TNode node) {
  Trace("fp-ppRewrite") << "TheoryFp::ppRewrite(): " << node << std::endl;

  Node res = node;
  
  // Abstract conversion functions
  if (node.getKind() == kind::FLOATINGPOINT_TO_REAL_TOTAL) {
    res = abstractFloatToReal(node);

    // Generate some lemmas
    NodeManager *nm = NodeManager::currentNM();

    Node pd = nm->mkNode(kind::IMPLIES,
			 nm->mkNode(kind::OR,
				    nm->mkNode(kind::FLOATINGPOINT_ISNAN, node[0]),
				    nm->mkNode(kind::FLOATINGPOINT_ISINF, node[0])),
			 nm->mkNode(kind::EQUAL, res, node[1]));
    handleLemma(pd);

    Node z = nm->mkNode(kind::IMPLIES,
			nm->mkNode(kind::FLOATINGPOINT_ISZ, node[0]),
			nm->mkNode(kind::EQUAL,
				   res,
				   nm->mkConst(Rational(0U))));
    handleLemma(z);

    // TODO : bounds on the output from largest floats

  } else if (node.getKind() == kind::FLOATINGPOINT_TO_FP_REAL) {
    res = abstractRealToFloat(node);

    // Generate some lemmas
    NodeManager *nm = NodeManager::currentNM();

    Node nnan = nm->mkNode(kind::NOT, nm->mkNode(kind::FLOATINGPOINT_ISNAN, res));
    handleLemma(nnan);

    Node z = nm->mkNode(kind::IMPLIES,
			nm->mkNode(kind::EQUAL,
				   node[1],
				   nm->mkConst(Rational(0U))),
			nm->mkNode(kind::EQUAL,
				   res,
				   nm->mkConst(FloatingPoint::makeZero(res.getType().getConst<FloatingPointSize>(), false))));
    handleLemma(z);

    // TODO : rounding-mode specific bounds on floats that don't give infinity
    // BEWARE of directed rounding!
  }
  
  if (res != node) {
    Trace("fp-ppRewrite") << "TheoryFp::ppRewrite(): node " << node << " rewritten to " << res << std::endl;
  }

  return res;
}

bool TheoryFp::refineAbstraction(TheoryModel *m, TNode abstract, TNode concrete) {
  Trace("fp-refineAbstraction") << "TheoryFp::refineAbstraction(): "
				<< abstract << " vs. " << concrete << std::endl;
  Kind k = concrete.getKind();
  if (k == kind::FLOATINGPOINT_TO_REAL_TOTAL) {
    // Get the values
    Assert(m->hasTerm(abstract));
    Assert(m->hasTerm(concrete[0]));
    Assert(m->hasTerm(concrete[1]));

    Node abstractValue = m->getValue(abstract);
    Node floatValue = m->getValue(concrete[0]);
    Node undefValue = m->getValue(concrete[1]);

    Assert(abstractValue.isConst());
    Assert(floatValue.isConst());
    Assert(undefValue.isConst());

    // Work out the actual value for those args
    NodeManager *nm = NodeManager::currentNM();

    Node evaluate = nm->mkNode(kind::FLOATINGPOINT_TO_REAL_TOTAL,
			       floatValue,
			       undefValue);
    Node concreteValue = Rewriter::rewrite(evaluate);
    Assert(concreteValue.isConst());

    Trace("fp-refineAbstraction") << "TheoryFp::refineAbstraction(): "
				  << concrete[0] << " = " << floatValue << std::endl
				  << "TheoryFp::refineAbstraction(): "
				  << concrete[1] << " = " << undefValue << std::endl
				  << "TheoryFp::refineAbstraction(): "
				  << abstract << " = " << abstractValue << std::endl
				  << "TheoryFp::refineAbstraction(): "
				  << concrete << " = " << concreteValue << std::endl;

    if (abstractValue != concreteValue) {
      // Need refinement lemmas
      // only in the normal and subnormal case
      Assert(floatValue.getConst<FloatingPoint>().isNormal() ||
	     floatValue.getConst<FloatingPoint>().isSubnormal());

      Node defined = nm->mkNode(kind::AND,
				nm->mkNode(kind::NOT,
					   nm->mkNode(kind::FLOATINGPOINT_ISNAN,
						      concrete[0])),
				nm->mkNode(kind::NOT,
					   nm->mkNode(kind::FLOATINGPOINT_ISINF,
						      concrete[0])));
      // First the "forward" constraints
      Node fg = nm->mkNode(kind::IMPLIES,
			   defined,
			   nm->mkNode(kind::EQUAL,
				      nm->mkNode(kind::FLOATINGPOINT_GEQ,
						 concrete[0],
						 floatValue),
				      nm->mkNode(kind::GEQ,
						 abstract,
						 concreteValue)));
      handleLemma(fg);

      Node fl = nm->mkNode(kind::IMPLIES,
			   defined,
			   nm->mkNode(kind::EQUAL,
				      nm->mkNode(kind::FLOATINGPOINT_LEQ,
						 concrete[0],
						 floatValue),
				      nm->mkNode(kind::LEQ,
						 abstract,
						 concreteValue)));
      handleLemma(fl);


      // Then the backwards constraints
      Node floatAboveAbstract =
	Rewriter::rewrite(nm->mkNode(kind::FLOATINGPOINT_TO_FP_REAL,
				     nm->mkConst(FloatingPointToFPReal(concrete[0].getType().getConst<FloatingPointSize>())),
				     nm->mkConst(roundTowardPositive),
				     abstractValue));

      Node bg = nm->mkNode(kind::IMPLIES,
			   defined,
			   nm->mkNode(kind::EQUAL,
				      nm->mkNode(kind::FLOATINGPOINT_GEQ,
						 concrete[0],
						 floatAboveAbstract),
				      nm->mkNode(kind::GEQ,
						 abstract,
						 abstractValue)));
      handleLemma(bg);


      Node floatBelowAbstract =
	Rewriter::rewrite(nm->mkNode(kind::FLOATINGPOINT_TO_FP_REAL,
				     nm->mkConst(FloatingPointToFPReal(concrete[0].getType().getConst<FloatingPointSize>())),
				     nm->mkConst(roundTowardNegative),
				     abstractValue));

      Node bl = nm->mkNode(kind::IMPLIES,
			   defined,
			   nm->mkNode(kind::EQUAL,
				      nm->mkNode(kind::FLOATINGPOINT_LEQ,
						 concrete[0],
						 floatBelowAbstract),
				      nm->mkNode(kind::LEQ,
						 abstract,
						 abstractValue)));
      handleLemma(bl);
      // TODO : see if the overflow conditions could be improved

      return true;

    } else {
      // No refinement needed
      return false;
    }
    
  } else if (k == kind::FLOATINGPOINT_TO_FP_REAL) {
    // Get the values
    Assert(m->hasTerm(abstract));
    Assert(m->hasTerm(concrete[0]));
    Assert(m->hasTerm(concrete[1]));

    Node abstractValue = m->getValue(abstract);
    Node rmValue = m->getValue(concrete[0]);
    Node realValue = m->getValue(concrete[1]);

    Assert(abstractValue.isConst());
    Assert(rmValue.isConst());
    Assert(realValue.isConst());

    // Work out the actual value for those args
    NodeManager *nm = NodeManager::currentNM();

    Node evaluate = nm->mkNode(kind::FLOATINGPOINT_TO_FP_REAL,
			       nm->mkConst(FloatingPointToFPReal(concrete.getType().getConst<FloatingPointSize>())),
			       rmValue,
			       realValue);
    Node concreteValue = Rewriter::rewrite(evaluate);
    Assert(concreteValue.isConst());

    Trace("fp-refineAbstraction") << "TheoryFp::refineAbstraction(): "
				  << concrete[0] << " = " << rmValue << std::endl
				  << "TheoryFp::refineAbstraction(): "
				  << concrete[1] << " = " << realValue << std::endl
				  << "TheoryFp::refineAbstraction(): "
				  << abstract << " = " << abstractValue << std::endl
				  << "TheoryFp::refineAbstraction(): "
				  << concrete << " = " << concreteValue << std::endl;

    if (abstractValue != concreteValue) {
      Assert(!abstractValue.getConst<FloatingPoint>().isNaN());
      Assert(!concreteValue.getConst<FloatingPoint>().isNaN());

      Node correctRoundingMode = nm->mkNode(kind::EQUAL, concrete[0], rmValue);
      // TODO : Generalise to all rounding modes

      // First the "forward" constraints
      Node fg = nm->mkNode(kind::IMPLIES,
			   correctRoundingMode,
			   nm->mkNode(kind::EQUAL,
				      nm->mkNode(kind::GEQ,
						 concrete[1],
						 realValue),
				      nm->mkNode(kind::FLOATINGPOINT_GEQ,
						 abstract,
						 concreteValue)));
      handleLemma(fg);

      Node fl = nm->mkNode(kind::IMPLIES,
			   correctRoundingMode,
			   nm->mkNode(kind::EQUAL,
				      nm->mkNode(kind::LEQ,
						 concrete[1],
						 realValue),
				      nm->mkNode(kind::FLOATINGPOINT_LEQ,
						 abstract,
						 concreteValue)));
      handleLemma(fl);



      // Then the backwards constraints
      if (!abstractValue.getConst<FloatingPoint>().isInfinite()) {
	Node realValueOfAbstract =
	  Rewriter::rewrite(nm->mkNode(kind::FLOATINGPOINT_TO_REAL_TOTAL,
				       abstractValue,
				       nm->mkConst(Rational(0U))));

	Node bg = nm->mkNode(kind::IMPLIES,
			     correctRoundingMode,
			     nm->mkNode(kind::EQUAL,
					nm->mkNode(kind::GEQ,
						   concrete[1],
						   realValueOfAbstract),
					nm->mkNode(kind::FLOATINGPOINT_GEQ,
						   abstract,
						   abstractValue)));
	handleLemma(bg);


	Node bl = nm->mkNode(kind::IMPLIES,
			     correctRoundingMode,
			     nm->mkNode(kind::EQUAL,
					nm->mkNode(kind::LEQ,
						   concrete[1],
						   realValueOfAbstract),
					nm->mkNode(kind::FLOATINGPOINT_LEQ,
						   abstract,
						   abstractValue)));
	handleLemma(bl);
      }

      return true;
    } else {
      // No refinement needed
      return false;
    }


  } else {
    Unreachable("Unknown abstraction");
  }

  return false;
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
    handleLemma(addA, false, true);
#else
    NodeManager *nm = NodeManager::currentNM();

    handleLemma(nm->mkNode(kind::EQUAL,
			   addA,
			   nm->mkConst(::CVC4::BitVector(1U, 1U))));
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
      handleLemma(nm->mkNode(kind::EQUAL, node, converted));
#else
      handleLemma(nm->mkNode(kind::EQUAL,
			      node,
			      nm->mkNode(kind::EQUAL,
					 converted,
					 nm->mkConst(::CVC4::BitVector(1U, 1U)))));
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

  } else if (node.getType().isBitVector()) {
    if (converted != node) {
      Assert(converted.getType().isBitVector());

      handleLemma(NodeManager::currentNM()->mkNode(kind::EQUAL, node, converted));

    } else {
      #if 0
      Assert((node.getKind() == kind::FLOATINGPOINT_COMPONENT_EXPONENT) ||
	     (node.getKind() == kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND) ||
	     (node.getKind() == kind::APPLY) ||  // For the UF we generate
	     (node.getKind() == kind::EQUAL));
      #endif
    }
  }

  return;
}

void TheoryFp::registerTerm(TNode node) {
  Trace("fp-registerTerm") << "TheoryFp::registerTerm(): " << node << std::endl;

  if (!isRegistered(node)) {
    bool success = registeredTerms.insert(node);
    Assert(success);

    // Add to the equality engine
    if (node.getKind() == kind::EQUAL) {
      equalityEngine.addTriggerEquality(node);
    } else {
      equalityEngine.addTerm(node);
    }

    convertAndEquateTerm(node);
  }
  return;
}

bool TheoryFp::isRegistered(TNode node) {
  return !(registeredTerms.find(node) == registeredTerms.end());
}

void TheoryFp::preRegisterTerm(TNode node) {
  Trace("fp-preRegisterTerm") << "TheoryFp::preRegisterTerm(): " << node << std::endl;
  registerTerm(node);
  return;
}

void TheoryFp::addSharedTerm(TNode node) {
  Trace("fp-addSharedTerm") << "TheoryFp::addSharedTerm(): " << node << std::endl;
  // A system-wide invariant; terms must be registered before they are shared
  Assert(isRegistered(node));
  return;
}

void TheoryFp::handleLemma(Node node) {
  Trace("fp") << "TheoryFp::handleLemma(): asserting " << node << std::endl;

  d_out->lemma(node,
	       false,
	       true);  // Has to be true because it contains embedded ITEs
  // Ignore the LemmaStatus structure for now...

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

  Trace("fp") << "TheoryFp::check(): started at effort level " << level << std::endl;

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
      Assert(!(predicate[0].getType().isFloatingPoint() ||
	       predicate[0].getType().isRoundingMode()) ||
	     isRegistered(predicate[0]));
      Assert(!(predicate[1].getType().isFloatingPoint() ||
	       predicate[1].getType().isRoundingMode()) ||
	     isRegistered(predicate[1]));
      registerTerm(predicate);            // Needed for float equalities

      if (negated) {
	Debug("fp-eq") << "TheoryFp::check(): adding dis-equality " << fact[0] << std::endl;
	equalityEngine.assertEquality(predicate, false, fact);
	
      } else {
	Debug("fp-eq") << "TheoryFp::check(): adding equality " << fact << std::endl;
	equalityEngine.assertEquality(predicate, true, fact);
      }
    } else {
      // A system-wide invariant; predicates are registered before they are asserted
      Assert(isRegistered(predicate));

      if (equalityEngine.isFunctionKind(predicate.getKind())) {
	Debug("fp-eq") << "TheoryFp::check(): adding predicate " << predicate << " is " << !negated << std::endl;
	equalityEngine.assertPredicate(predicate, !negated, fact);
      }
    }


  }


  // Resolve the abstractions for the conversion lemmas
  //  if (level == EFFORT_COMBINATION) {
  if (level == EFFORT_LAST_CALL) {
    Trace("fp") << "TheoryFp::check(): checking abstractions" << std::endl;
    TheoryModel *m = getValuation().getModel();
    bool lemmaAdded = false;
    
    for (abstractionMapType::const_iterator i = abstractionMap.begin();
	 i != abstractionMap.end();
	 ++i) {
      if (m->hasTerm((*i).first)) { // Is actually used in the model
	lemmaAdded |= refineAbstraction(m, (*i).first, (*i).second);
      }
    }
  }

  
  Trace("fp") << "TheoryFp::check(): completed" << std::endl;

  /* Checking should be handled by the bit-vector engine */
  return;

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

  void TheoryFp::collectModelInfo(TheoryModel *m) {
    std::set<Node> relevantTerms;

    Trace("fp-collectModelInfo") << "TheoryFp::collectModelInfo(): begin" << std::endl;

    // Work out which variables are needed
    computeRelevantTerms(relevantTerms);

    if (Trace.isOn("fp-collectModelInfo")) {
      for (std::set<Node>::const_iterator i(relevantTerms.begin());
	   i != relevantTerms.end();
	   ++i) {
	Trace("fp-collectModelInfo") << "TheoryFp::collectModelInfo(): relevantTerms " << *i << std::endl;
      }
    }


    std::set<TNode> visited;
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
    Debug("fp-eq") << "TheoryFp::eqNotifyTriggerEquality(): call back as equality " << equality << " is " << value << std::endl;

    if (value) {
      return theorySolver.handlePropagation(equality);
    } else {
      return theorySolver.handlePropagation(equality.notNode());
    }
  }

  bool TheoryFp::NotifyClass::eqNotifyTriggerPredicate(TNode predicate, bool value) {
    Debug("fp-eq") << "TheoryFp::eqNotifyTriggerPredicate(): call back as predicate " << predicate << " is " << value << std::endl;

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
