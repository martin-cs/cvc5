/*********************                                                        */
/*! \file fp_converter.cpp
 ** \verbatim
 ** Original author: Martin Brain
 ** Major contributors: 
 ** Minor contributors (to current version): 
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2014  University of Oxford
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Conversion of floating-point operations to bit-vectors using symfpu. ]]
 **
 **/

// Only needed for the leaf test
#include "theory/theory.h"

#include "theory/fp/fp_converter.h"

#include <stack>

#include "symfpu/core/packing.h"
#include "symfpu/core/sign.h"
#include "symfpu/core/add.h"
#include "symfpu/core/multiply.h"
#include "symfpu/core/fma.h"
#include "symfpu/core/sqrt.h"
#include "symfpu/core/divide.h"
#include "symfpu/core/compare.h"
#include "symfpu/core/classify.h"
#include "symfpu/core/convert.h"

#if 0
// \todo Fix this ugly hack
// So, the problem is that the CVC4 back-end is not just a .h file, it
// also requires some code.  This code, currently, should sit in the
// symfpu repository.  But it can't be built there because it needs
// the CVC4 infrastructure and I don't want to get the CVC4 build to
// run make in that directory and patch things together.  So ...

#include "symfpu/baseTypes/cvc4_symbolic.cpp"
#include "symfpu/baseTypes/cvc4_literal.cpp"
#endif

namespace CVC4 {
namespace theory {
namespace fp {

#if 0
  // Test that the basic operations provided by the back-ends are
  // equivalent
  static testOperations (unsigned width) {

    Assert(width < 32);

    // Unsigned
    unsigned limit = (1 << width) - 1;
    for (unsigned i = 0; i <= limit; ++i) {
      for (unsigned j = 0; j <= limit; ++j) {
	simpleExecutable::traits::ubv first(i);
	simpleExecutable::traits::ubv second(i);

	// Compute results of operation

	// The same for the other ones
	// convert!
      }
    }


  }


  static void testMultiply (void) {
    symfpuSymbolic::fpt format(8,24);

    symfpuSymbolic::rm rne(symfpuSymbolic::traits::RNE());

    Node one(NodeManager::currentNM()->mkConst(BitVector(32, 0x3f800000U)));
    symfpuSymbolic::ubv oneUBV(one);
    symfpuSymbolic::uf oneUF(symfpu::unpack<symfpuSymbolic::traits>(format, oneUBV));
	     

    // 0b00000000010110001000010000010001
    Node two(NodeManager::currentNM()->mkConst(BitVector(32, 0x00588411U)));
    symfpuSymbolic::ubv twoUBV(two);
    symfpuSymbolic::uf twoUF(symfpu::unpack<symfpuSymbolic::traits>(format, twoUBV));

    symfpuSymbolic::uf mult(symfpu::multiply<symfpuSymbolic::traits>(format, rne, oneUF, twoUF));

    return;
  }
#endif
  

  fpConverter::fpConverter (context::UserContext* user) :
    f(user), r(user), b(user), u(user), s(user), 
    roundingModeUF(Node::null()),
    NaNMap(user), infMap(user), zeroMap(user),
    signMap(user), exponentMap(user), significandMap(user),
    additionalAssertions(user)
  {
    //    testMultiply();
  }





  Node fpConverter::buildRoundingModeUFApp (Node node) {
    Assert(node.isVar());
    Assert(node.getType().isRoundingMode());

    NodeManager *nm = NodeManager::currentNM();
    if (roundingModeUF == Node::null()) {
      roundingModeUF = nm->mkSkolem("roundingMode_to_BV",
				    nm->mkFunctionType(nm->roundingModeType(),
						       nm->mkBitVectorType(NUMRM)),
				    "roundingMode_to_BV",
				    NodeManager::SKOLEM_EXACT_NAME);
    }
    return nm->mkNode(kind::APPLY_UF, roundingModeUF, node);
  }


  Node fpConverter::buildNaNUFApp (Node node) {
    Assert(node.isVar());
    TypeNode t(node.getType());
    Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

    NodeManager *nm = NodeManager::currentNM();
    uninterprettedFunctionMap::const_iterator i(NaNMap.find(t));

    Node fun;
    if (i == NaNMap.end()) {
      fun = nm->mkSkolem("floating_point_to_BV_NaN",
			 nm->mkFunctionType(t, nm->booleanType()),
			 "floating_point_to_BV_NaN",
			 NodeManager::SKOLEM_EXACT_NAME);
      NaNMap.insert(t,fun);
    } else {
      fun = (*i).second;
    }
    return nm->mkNode(kind::APPLY_UF, fun, node);
  }


  Node fpConverter::buildInfUFApp (Node node) {
    Assert(node.isVar());
    TypeNode t(node.getType());
    Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

    NodeManager *nm = NodeManager::currentNM();
    uninterprettedFunctionMap::const_iterator i(infMap.find(t));

    Node fun;
    if (i == infMap.end()) {
      fun = nm->mkSkolem("floating_point_to_BV_inf",
			 nm->mkFunctionType(t, nm->booleanType()),
			 "floating_point_to_BV_inf",
			 NodeManager::SKOLEM_EXACT_NAME);
      infMap.insert(t,fun);
    } else {
      fun = (*i).second;
    }
    return nm->mkNode(kind::APPLY_UF, fun, node);
  }


  Node fpConverter::buildZeroUFApp (Node node) {
    Assert(node.isVar());
    TypeNode t(node.getType());
    Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

    NodeManager *nm = NodeManager::currentNM();
    uninterprettedFunctionMap::const_iterator i(zeroMap.find(t));

    Node fun;
    if (i == zeroMap.end()) {
      fun = nm->mkSkolem("floating_point_to_BV_zero",
			 nm->mkFunctionType(t, nm->booleanType()),
			 "floating_point_to_BV_zero",
			 NodeManager::SKOLEM_EXACT_NAME);
      zeroMap.insert(t,fun);
    } else {
      fun = (*i).second;
    }
    return nm->mkNode(kind::APPLY_UF, fun, node);
  }

  Node fpConverter::buildSignUFApp (Node node) {
    Assert(node.isVar());
    TypeNode t(node.getType());
    Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

    NodeManager *nm = NodeManager::currentNM();
    uninterprettedFunctionMap::const_iterator i(signMap.find(t));

    Node fun;
    if (i == signMap.end()) {
      fun = nm->mkSkolem("floating_point_to_BV_sign",
			 nm->mkFunctionType(t, nm->booleanType()),
			 "floating_point_to_BV_sign",
			 NodeManager::SKOLEM_EXACT_NAME);
      signMap.insert(t,fun);
    } else {
      fun = (*i).second;
    }
    return nm->mkNode(kind::APPLY_UF, fun, node);
  }


  Node fpConverter::buildExponentUFApp (Node node) {
    Assert(node.isVar());
    TypeNode t(node.getType());
    Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

    NodeManager *nm = NodeManager::currentNM();
    uninterprettedFunctionMap::const_iterator i(exponentMap.find(t));

    Node fun;
    if (i == exponentMap.end()) {
      traits::fpt fmt(t);
      fun = nm->mkSkolem("floating_point_to_BV_exponent",
			 nm->mkFunctionType(t, nm->mkBitVectorType(uf::exponentWidth(fmt))),
			 "floating_point_to_BV_exponent",
			 NodeManager::SKOLEM_EXACT_NAME);
      exponentMap.insert(t,fun);
    } else {
      fun = (*i).second;
    }
    return nm->mkNode(kind::APPLY_UF, fun, node);
  }

  Node fpConverter::buildSignificandUFApp (Node node) {
    Assert(node.isVar());
    TypeNode t(node.getType());
    Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

    NodeManager *nm = NodeManager::currentNM();
    uninterprettedFunctionMap::const_iterator i(significandMap.find(t));

    Node fun;
    if (i == significandMap.end()) {
      traits::fpt fmt(t);
      fun = nm->mkSkolem("floating_point_to_BV_significand",
			 nm->mkFunctionType(t, nm->mkBitVectorType(uf::significandWidth(fmt))),
			 "floating_point_to_BV_significand",
			 NodeManager::SKOLEM_EXACT_NAME);
      significandMap.insert(t,fun);
    } else {
      fun = (*i).second;
    }
    return nm->mkNode(kind::APPLY_UF, fun, node);
  }



  // Non-convertible things should only be added to the stack at the very start, thus...
  #define PASSTHROUGH   Assert(workStack.empty())


  TNode fpConverter::convert (TNode node) {
    std::stack<TNode> workStack;
    TNode result = node;

    workStack.push(node);

    while (!workStack.empty()) {
      TNode current = workStack.top();
      workStack.pop();
      result = current;


      TypeNode t(current.getType());

      if (t.isRoundingMode()) {
	rmMap::const_iterator i(r.find(current));
	
	if (i == r.end()) {
	  if (Theory::isLeafOf(current, THEORY_FP)) {

	    if (current.getKind() == kind::CONST_ROUNDINGMODE) {

	      /******** Constants ********/
	      switch (current.getConst<RoundingMode>()) {
	      case roundNearestTiesToEven : r.insert(current, traits::RNE()); break;
	      case roundNearestTiesToAway : r.insert(current, traits::RNA()); break;
	      case roundTowardPositive : r.insert(current, traits::RTP()); break;
	      case roundTowardNegative : r.insert(current, traits::RTN()); break;
	      case roundTowardZero : r.insert(current, traits::RTZ()); break;
	      default :	Unreachable("Unknown rounding mode"); break;
	      }

	    } else {
	      /******** Variables ********/
	      //rm tmp(symfpu::NONDET);
	      //rm tmp(buildRoundingModeUFApp(current));
	      rm tmp(NodeManager::currentNM()->mkNode(kind::ROUNDINGMODE_BITBLAST, current));
	      r.insert(current, tmp);
	      additionalAssertions.push_back(tmp.valid().getNode());

	    }

	  } else {
	    Unreachable("Unknown kind of type RoundingMode");
	  }
	}
	// Returns a rounding-mode type so don't alter the return value

      } else if (t.isFloatingPoint()) {

	fpMap::const_iterator i(f.find(current));
	
	if (i == f.end()) {

	  if (Theory::isLeafOf(current, THEORY_FP)) {
	    if (current.getKind() == kind::CONST_FLOATINGPOINT) {
	      /******** Constants ********/
	      f.insert(current, symfpu::unpackedFloat<traits>( current.getConst<FloatingPoint>().getLiteral() ));


	    } else {
	      /******** Variables ********/
	      //symfpu::unpackedFloat<traits> tmp(symfpu::NONDET, fpt(current.getType()));
	      /*
		symfpu::unpackedFloat<traits>
		  tmp(buildNaNUFApp(current),
		      buildInfUFApp(current),
		      buildZeroUFApp(current),
		      buildSignUFApp(current),
		      buildExponentUFApp(current),
		      buildSignificandUFApp(current));
	    */
	      NodeManager *nm = NodeManager::currentNM();
	      symfpu::unpackedFloat<traits>
		tmp(nm->mkNode(kind::FLOATINGPOINT_COMPONENT_NAN, current),
		    nm->mkNode(kind::FLOATINGPOINT_COMPONENT_INF, current),
		    nm->mkNode(kind::FLOATINGPOINT_COMPONENT_ZERO, current),
		    nm->mkNode(kind::FLOATINGPOINT_COMPONENT_SIGN, current),
		    nm->mkNode(kind::FLOATINGPOINT_COMPONENT_EXPONENT, current),
		    nm->mkNode(kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND, current));
	      f.insert(current, tmp);
	      additionalAssertions.push_back(tmp.valid(fpt(current.getType())).getNode());
	    }

	  } else {

	    switch (current.getKind()) {
	    case kind::CONST_FLOATINGPOINT :
	    case kind::VARIABLE :
	    case kind::BOUND_VARIABLE :
	    case kind::SKOLEM :
	      // Unreachable("Kind " + kindToString(current.getKind()) + " should have been handled as a leaf.");
	      Unreachable("Kind should have been handled as a leaf.");
	      break;
	      
	      /******** Operations ********/
	    case kind::FLOATINGPOINT_ABS :
	    case kind::FLOATINGPOINT_NEG :
	      {
		fpMap::const_iterator arg1(f.find(current[0]));
		
		if (arg1 == f.end()) {
		  workStack.push(current);
		  workStack.push(current[0]);
		  continue;    // i.e. recurse!
		}
		
		switch (current.getKind()) {
		case kind::FLOATINGPOINT_ABS :
		  f.insert(current, symfpu::absolute<traits>(fpt(current.getType()), (*arg1).second));
		  break;
		case kind::FLOATINGPOINT_NEG :
		  f.insert(current, symfpu::negate<traits>(fpt(current.getType()), (*arg1).second));
		  break;
		default :
		  Unreachable("Unknown unary floating-point function");
		  break;
		}
		
	      }
	      break;

	    case kind::FLOATINGPOINT_SQRT :
	      {
		rmMap::const_iterator mode(r.find(current[0]));
		fpMap::const_iterator arg1(f.find(current[1]));
		bool recurseNeeded = (mode == r.end()) || (arg1 == f.end());
	      
		if (recurseNeeded) {
		  workStack.push(current);
		  if (mode == r.end()) { workStack.push(current[0]); }
		  if (arg1 == f.end()) { workStack.push(current[1]); }
		  continue;    // i.e. recurse!
		}

		switch (current.getKind()) {
		case kind::FLOATINGPOINT_SQRT :
		  f.insert(current, symfpu::sqrt<traits>(fpt(current.getType()),
							(*mode).second,
							 (*arg1).second));
		  break;
		default :
		  Unreachable("Unknown unary rounded floating-point function");
		  break;
		}
	      }
	      break;

	    case kind::FLOATINGPOINT_MIN :
	    case kind::FLOATINGPOINT_MAX :
	      {
		fpMap::const_iterator arg1(f.find(current[0]));
		fpMap::const_iterator arg2(f.find(current[1]));
		bool recurseNeeded = (arg1 == f.end()) || (arg2 == f.end());
	      
		if (recurseNeeded) {
		  workStack.push(current);
		  if (arg1 == f.end()) { workStack.push(current[0]); }
		  if (arg2 == f.end()) { workStack.push(current[1]); }
		  continue;    // i.e. recurse!
		}

		switch (current.getKind()) {
		case kind::FLOATINGPOINT_MAX :
		  f.insert(current, symfpu::max<traits>(fpt(current.getType()),
							(*arg1).second,
							(*arg2).second));
		  break;
		  
		case kind::FLOATINGPOINT_MIN :
		  f.insert(current, symfpu::max<traits>(fpt(current.getType()),
							(*arg1).second,
							(*arg2).second));
		  break;

		default :
		  Unreachable("Unknown binary floating-point function");
		  break;
		}
	      }
	      break;
	      
	      
	    case kind::FLOATINGPOINT_PLUS :
	    case kind::FLOATINGPOINT_SUB :
	    case kind::FLOATINGPOINT_MULT :
	    case kind::FLOATINGPOINT_DIV :
	      {
		rmMap::const_iterator mode(r.find(current[0]));
		fpMap::const_iterator arg1(f.find(current[1]));
		fpMap::const_iterator arg2(f.find(current[2]));
		bool recurseNeeded = (mode == r.end()) || (arg1 == f.end()) || (arg2 == f.end());
	      
		if (recurseNeeded) {
		  workStack.push(current);
		  if (mode == r.end()) { workStack.push(current[0]); }
		  if (arg1 == f.end()) { workStack.push(current[1]); }
		  if (arg2 == f.end()) { workStack.push(current[2]); }
		  continue;    // i.e. recurse!
		}

		switch (current.getKind()) {
		case kind::FLOATINGPOINT_PLUS :
		  f.insert(current, symfpu::add<traits>(fpt(current.getType()),
							(*mode).second,
							(*arg1).second,
							(*arg2).second,
							prop(true)));
		  break;
		  
		case kind::FLOATINGPOINT_SUB :
		  // Should have been removed by the rewriter
		  Unreachable("Floating-point subtraction should be removed by the rewriter.");
		  f.insert(current, symfpu::add<traits>(fpt(current.getType()),
							(*mode).second,
							(*arg1).second,
							(*arg2).second,
							prop(false)));
		  break;

		case kind::FLOATINGPOINT_MULT :
		  f.insert(current, symfpu::multiply<traits>(fpt(current.getType()),
							     (*mode).second,
							     (*arg1).second,
							     (*arg2).second));
		  break;
		case kind::FLOATINGPOINT_DIV :
		  f.insert(current, symfpu::divide<traits>(fpt(current.getType()),
							     (*mode).second,
							     (*arg1).second,
							     (*arg2).second));
		  break;
		default :
		  Unreachable("Unknown binary rounded floating-point function");
		  break;
		}
	      }
	      break;

	    case kind::FLOATINGPOINT_FMA :
	      {
		rmMap::const_iterator mode(r.find(current[0]));
		fpMap::const_iterator arg1(f.find(current[1]));
		fpMap::const_iterator arg2(f.find(current[2]));
		fpMap::const_iterator arg3(f.find(current[3]));
		bool recurseNeeded = (mode == r.end()) || (arg1 == f.end()) || (arg2 == f.end() || (arg3 == f.end()));
	      
		if (recurseNeeded) {
		  workStack.push(current);
		  if (mode == r.end()) { workStack.push(current[0]); }
		  if (arg1 == f.end()) { workStack.push(current[1]); }
		  if (arg2 == f.end()) { workStack.push(current[2]); }
		  if (arg3 == f.end()) { workStack.push(current[3]); }
		  continue;    // i.e. recurse!
		}

		f.insert(current, symfpu::fma<traits>(fpt(current.getType()),
						      (*mode).second,
						      (*arg1).second,
						      (*arg2).second,
						      (*arg3).second));
	      }
	      break;

	    
	    case kind::FLOATINGPOINT_REM :
	    case kind::FLOATINGPOINT_RTI :
	      Unimplemented("Operation not yet supported in symfpu");
	      break;
	      
	      /******** Conversions ********/
	    case kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT :
	      {
		rmMap::const_iterator mode(r.find(current[0]));
		fpMap::const_iterator arg1(f.find(current[1]));
		bool recurseNeeded = (mode == r.end()) || (arg1 == f.end());
	      
		if (recurseNeeded) {
		  workStack.push(current);
		  if (mode == r.end()) { workStack.push(current[0]); }
		  if (arg1 == f.end()) { workStack.push(current[1]); }
		  continue;    // i.e. recurse!
		}
		
		f.insert(current, symfpu::convertFloatToFloat<traits>(fpt(current[1].getType()),
								      fpt(current.getType()),
								      (*mode).second,
								      (*arg1).second));
	      }
	      break;


	    case kind::FLOATINGPOINT_FP :
	    case kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR :
	    case kind::FLOATINGPOINT_TO_FP_REAL :
	    case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR :
	    case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR :
	      Unimplemented("Conversion not finished");
	      break;
	      
	    case kind::FLOATINGPOINT_TO_FP_GENERIC :
	      Unreachable("Generic to_fp not removed");
	      break;
	      
	    default :
	      Unreachable("Unknown kind of type FloatingPoint");
	      break;
	    }
	  }
	}
	// Returns a floating-point type so don't alter the return value

      } else if (t.isBoolean()) {

	boolMap::const_iterator i(b.find(current));
	  
	if (i == b.end()) {
	    
	  switch (current.getKind()) {
	    /******** Comparisons ********/
	  case kind::EQUAL :
	    {
	      TypeNode childType (current[0].getType());

	      if (childType.isFloatingPoint()) {
		fpMap::const_iterator arg1(f.find(current[0]));
		fpMap::const_iterator arg2(f.find(current[1]));
		bool recurseNeeded = (arg1 == f.end()) || (arg2 == f.end());
		  
		if (recurseNeeded) {
		  workStack.push(current);
		  if (arg1 == f.end()) { workStack.push(current[0]); }
		  if (arg2 == f.end()) { workStack.push(current[1]); }
		  continue;    // i.e. recurse!
		}

		b.insert(current, symfpu::smtlibEqual<traits>(fpt(childType),
							      (*arg1).second,
							      (*arg2).second));

	      } else if (childType.isRoundingMode()) {
		rmMap::const_iterator arg1(r.find(current[0]));
		rmMap::const_iterator arg2(r.find(current[1]));
		bool recurseNeeded = (arg1 == r.end()) || (arg2 == r.end());
		  
		if (recurseNeeded) {
		  workStack.push(current);
		  if (arg1 == r.end()) { workStack.push(current[0]); }
		  if (arg2 == r.end()) { workStack.push(current[1]); }
		  continue;    // i.e. recurse!
		}

		b.insert(current, (*arg1).second == (*arg2).second);


	      } else {
		PASSTHROUGH;
		return result;
	      }
	    }
	    break;

	  case kind::FLOATINGPOINT_LEQ :
	  case kind::FLOATINGPOINT_LT :
	    {
      	      TypeNode childType (current[0].getType());

	      fpMap::const_iterator arg1(f.find(current[0]));
	      fpMap::const_iterator arg2(f.find(current[1]));
	      bool recurseNeeded = (arg1 == f.end()) || (arg2 == f.end());
	      
	      if (recurseNeeded) {
		workStack.push(current);
		if (arg1 == f.end()) { workStack.push(current[0]); }
		if (arg2 == f.end()) { workStack.push(current[1]); }
		continue;    // i.e. recurse!
	      }

	      switch (current.getKind()) {
	      case kind::FLOATINGPOINT_LEQ :
		b.insert(current, symfpu::lessThanOrEqual<traits>(fpt(childType),
								  (*arg1).second,
								  (*arg2).second));
		break;

	      case kind::FLOATINGPOINT_LT :
		b.insert(current, symfpu::lessThan<traits>(fpt(childType),
							   (*arg1).second,
							   (*arg2).second));
		break;

	      default :
		Unreachable("Unknown binary floating-point relation");
		break;

	      }
	    }
	    break;
	      
	  case kind::FLOATINGPOINT_ISN :
	  case kind::FLOATINGPOINT_ISSN :
	  case kind::FLOATINGPOINT_ISZ :
	  case kind::FLOATINGPOINT_ISINF :
	  case kind::FLOATINGPOINT_ISNAN :
	  case kind::FLOATINGPOINT_ISNEG :
	  case kind::FLOATINGPOINT_ISPOS :
	    {
      	      TypeNode childType (current[0].getType());
	      fpMap::const_iterator arg1(f.find(current[0]));

	      if (arg1 == f.end()) {
		workStack.push(current);
		workStack.push(current[0]);
		continue;    // i.e. recurse!
	      }

	      switch (current.getKind()) {
	      case kind::FLOATINGPOINT_ISN :
		b.insert(current, symfpu::isNormal<traits>(fpt(childType),
							   (*arg1).second));
		break;

	      case kind::FLOATINGPOINT_ISSN :
		b.insert(current, symfpu::isSubnormal<traits>(fpt(childType),
							      (*arg1).second));
		break;

	      case kind::FLOATINGPOINT_ISZ :
		b.insert(current, symfpu::isZero<traits>(fpt(childType),
							 (*arg1).second));
		break;

	      case kind::FLOATINGPOINT_ISINF :
		b.insert(current, symfpu::isInfinite<traits>(fpt(childType),
							     (*arg1).second));
		break;

	      case kind::FLOATINGPOINT_ISNAN :
		b.insert(current, symfpu::isNaN<traits>(fpt(childType),
							(*arg1).second));
		break;

	      case kind::FLOATINGPOINT_ISPOS :
		b.insert(current, symfpu::isPositive<traits>(fpt(childType),
							     (*arg1).second));
		break;

	      case kind::FLOATINGPOINT_ISNEG :
		b.insert(current, symfpu::isNegative<traits>(fpt(childType),
							     (*arg1).second));
		break;

	      default :
		Unreachable("Unknown unary floating-point relation");
		break;

	      }
	    }
	    break;

	  case kind::FLOATINGPOINT_EQ :
	  case kind::FLOATINGPOINT_GEQ :
	  case kind::FLOATINGPOINT_GT :
	    Unreachable("Kind should have been removed by rewriter.");
	    break;

	    // Components will be registered as they are owned by
	    // the floating-point theory.  No action is required.
	  case kind::FLOATINGPOINT_COMPONENT_NAN :
	  case kind::FLOATINGPOINT_COMPONENT_INF :
	  case kind::FLOATINGPOINT_COMPONENT_ZERO :
	  case kind::FLOATINGPOINT_COMPONENT_SIGN :
	    /* Fall through... */

	  default :
	    PASSTHROUGH;
	    return result;
	    break;
	  }

	  i = b.find(current);
	}

	result = (*i).second.getNode();

      } else if (t.isBitVector()) {

	switch (current.getKind()) {
	  /******** Conversions ********/
	case kind::FLOATINGPOINT_TO_UBV :
	  {
	    TypeNode childType (current[0].getType());
	    ubvMap::const_iterator i(u.find(current));
	      
	    if (i == u.end()) {
	      rmMap::const_iterator mode(r.find(current[0]));
	      fpMap::const_iterator arg1(f.find(current[1]));
	      bool recurseNeeded = (mode == r.end()) || (arg1 == f.end());
		
	      if (recurseNeeded) {
		workStack.push(current);
		if (mode == r.end()) { workStack.push(current[0]); }
		if (arg1 == f.end()) { workStack.push(current[1]); }
		continue;    // i.e. recurse!
	      }
		
	      Unimplemented("Operation not yet supported in symfpu");
	      /*
		u.insert(current, symfpu::toUnsigned<traits>(fpt(childType),
		(*mode).second,
		(*arg1).second));
	      */
	      i = u.find(current);
	    }
	      
	    result = (*i).second.getNode();
	  }
	  break;

	case kind::FLOATINGPOINT_TO_SBV :
	  {
	    TypeNode childType (current[0].getType());
	    sbvMap::const_iterator i(s.find(current));
	      
	    if (i == s.end()) {
	      rmMap::const_iterator mode(r.find(current[0]));
	      fpMap::const_iterator arg1(f.find(current[1]));
	      bool recurseNeeded = (mode == r.end()) || (arg1 == f.end());
	      
	      if (recurseNeeded) {
		workStack.push(current);
		if (mode == r.end()) { workStack.push(current[0]); }
		if (arg1 == f.end()) { workStack.push(current[1]); }
		continue;    // i.e. recurse!
	      }

	      Unimplemented("Operation not yet supported in symfpu");
	      /*
		s.insert(current, symfpu::toSigned<traits>(fpt(childType),
		(*mode).second,
		(*arg1).second));
	      */
	      i = s.find(current);
	    }

	    result = (*i).second.getNode();
	  }
	  break;

	  // Again, no action is needed
	case kind::FLOATINGPOINT_COMPONENT_EXPONENT :
	case kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND :
	case kind::ROUNDINGMODE_BITBLAST :
	  /* Fall through ... */
      
	default :
	  PASSTHROUGH;
	  break;
	}

      } else if (t.isReal()) {

	switch (current.getKind()) {
	  /******** Conversions ********/
	case kind::FLOATINGPOINT_TO_REAL :
	  Unimplemented("Conversion from floating-point to real not supported with bit-blasting theory solver");
	  break;

	default :
	  PASSTHROUGH;
	  break;
	}

      } else {
	PASSTHROUGH;
      }
    }

    return result;
  }


  Node fpConverter::getValue (Valuation &val, TNode var) {
    // Should be checking if it is a meta-kind variable and one of our types
    // OR one of our types and kind is not one of our interpretted functions
    //  isLeaf() should work, apparently
    Assert((var.getKind() == kind::VARIABLE) ||
	   (var.getKind() == kind::BOUND_VARIABLE) ||
	   (var.getKind() == kind::SELECT) ||
	   (var.getKind() == kind::SKOLEM));

    TypeNode t(var.getType());

    if (t.isRoundingMode()) {
      rmMap::const_iterator i(r.find(var));
      
      if (i == r.end()) {
	Unreachable("Asking for the value of an unregistered expression");
      } else {
	Node rmValue = val.getModelValue((*i).second.getNode());
	Assert(rmValue.isConst());
	Assert(rmValue.getType().getKind() == kind::BITVECTOR_TYPE);
	
	BitVector rmBVValue(rmValue.getConst<BitVector>());
	
	if (rmBVValue == traits::RNE().getNode().getConst<BitVector>()) {
	  return NodeManager::currentNM()->mkConst(roundNearestTiesToEven);
	} else if (rmBVValue == traits::RNA().getNode().getConst<BitVector>()) {
	  return NodeManager::currentNM()->mkConst(roundNearestTiesToAway);
	} else if (rmBVValue == traits::RTP().getNode().getConst<BitVector>()) {
	  return NodeManager::currentNM()->mkConst(roundTowardPositive);
	} else if (rmBVValue == traits::RTN().getNode().getConst<BitVector>()) {
	  return NodeManager::currentNM()->mkConst(roundTowardNegative);
	} else if (rmBVValue == traits::RTZ().getNode().getConst<BitVector>()) {
	  return NodeManager::currentNM()->mkConst(roundTowardZero);
	} else {
	  Unreachable("Bit-vector corresponding to a rounding mode contains an unrecognised value");
	}
      }

    } else if (t.isFloatingPoint()) {

      fpMap::const_iterator i(f.find(var));
      
      if (i == f.end()) {
	Unreachable("Asking for the value of an unregistered expression");
      } else {
	Node nanValue = val.getModelValue((*i).second.nan.getNode());
	Assert(nanValue.isConst());
	Assert(nanValue.getType().isBoolean());
	
	Node infValue = val.getModelValue((*i).second.inf.getNode());
	Assert(infValue.isConst());
	Assert(infValue.getType().isBoolean());

	Node zeroValue = val.getModelValue((*i).second.zero.getNode());
	Assert(zeroValue.isConst());
	Assert(zeroValue.getType().isBoolean());

	Node signValue = val.getModelValue((*i).second.sign.getNode());
	Assert(signValue.isConst());
	Assert(signValue.getType().isBoolean());

	Node exponentValue = val.getModelValue((*i).second.exponent.getNode());
	Assert(exponentValue.isConst());
	Assert(exponentValue.getType().isBitVector());

	Node significandValue = val.getModelValue((*i).second.significand.getNode());
	Assert(significandValue.isConst());
	Assert(significandValue.getType().isBitVector());

	FloatingPointLiteral fpl(nanValue.getConst<bool>(),
				 infValue.getConst<bool>(),
				 zeroValue.getConst<bool>(),
				 signValue.getConst<bool>(),
				 exponentValue.getConst<BitVector>(),
				 significandValue.getConst<BitVector>());
	return NodeManager::currentNM()->mkConst(FloatingPoint(var.getType().getConst<FloatingPointSize>(), fpl));
      }

    } else {
      Unreachable("Asking for the value of a type that is not managed by the floating-point theory");
    }


    Unreachable("Unable to find value");
    return Node::null();
  }


}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */



#if 0
  // Need an expand definition which enables bit-vectors when needed





  void TheoryFp::preRegisterTerm(TNode node) {
    // Don't recurse!

    // Things can be registered multiple times -- be careful
    // addSharedTerm needed as well
    // staticLearning is early and gets the full thing
    // Lemma to add

    Trace("fp") << "TheoryFp::preRegisterTerm(): " << node << std::endl;

    return;

  }/* TheoryFp::preRegisterTerm() */

#endif
