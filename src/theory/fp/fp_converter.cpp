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
#include "symfpu/core/remainder.h"


namespace CVC4 {
namespace theory {
namespace fp {


  size_t PairTypeNodeHashFunction::operator()(const std::pair<TypeNode, TypeNode> &p) const {
    TypeNodeHashFunction h;
    return h(p.first) ^ h(p.second);
  }

  

  fpConverter::fpConverter (context::UserContext* user) :
    f(user), r(user), b(user), u(user), s(user), 
    additionalAssertions(user)
  {
  }

  Node fpConverter::ufToNode (const fpt &format, const uf &u) const {
    NodeManager *nm = NodeManager::currentNM();

    FloatingPointSize fps(format.getTypeNode().getConst<FloatingPointSize>());

    // This is not entirely obvious but it builds a float from components
    // Particularly, if the components can be constant folded, it should
    // build a Node containing a constant FloatingPoint number

    ubv packed(symfpu::pack<traits>(format, u));
    Node value = nm->mkNode(nm->mkConst(FloatingPointToFPIEEEBitVector(fps)),
			    packed.getNode());
    return value;
  }

  Node fpConverter::rmToNode (const rm &r) const {
    NodeManager *nm = NodeManager::currentNM();

    Node transVar = r.getNode();

    Node RNE = traits::RNE().getNode();
    Node RNA = traits::RNA().getNode();
    Node RTP = traits::RTP().getNode();
    Node RTN = traits::RTN().getNode();
    Node RTZ = traits::RTZ().getNode();

    Node value =
      nm->mkNode(kind::ITE,
		 nm->mkNode(kind::EQUAL, transVar, RNE),
		 nm->mkConst(roundNearestTiesToEven),
		 nm->mkNode(kind::ITE,
			    nm->mkNode(kind::EQUAL, transVar, RNA),
			    nm->mkConst(roundNearestTiesToAway),
			    nm->mkNode(kind::ITE,
				       nm->mkNode(kind::EQUAL, transVar, RTP),
				       nm->mkConst(roundTowardPositive),
				       nm->mkNode(kind::ITE,
						  nm->mkNode(kind::EQUAL, transVar, RTN),
						  nm->mkConst(roundTowardNegative),
						  nm->mkConst(roundTowardZero)))));
    return value;
  }

  Node fpConverter::propToNode (const prop &p) const {
#ifdef SYMFPUPROPISBOOL
    Node value = p.getNode();
#else
    NodeManager *nm = NodeManager::currentNM();
    Node value = nm->mkNode(kind::EQUAL,
			    p.getNode(),
			    nm->mkConst(::CVC4::BitVector(1U, 1U)));
#endif
    return value;
  }
  Node fpConverter::ubvToNode (const ubv &u) const {
    return u.getNode();
  }
  Node fpConverter::sbvToNode (const sbv &s) const {
    return s.getNode();
  }


  // Creates the components constraint
  fpConverter::uf fpConverter::buildComponents(TNode current) {
    Assert(Theory::isLeafOf(current, THEORY_FP) ||
	   current.getKind() == kind::FLOATINGPOINT_TO_FP_REAL);


    NodeManager *nm = NodeManager::currentNM();
    uf tmp(nm->mkNode(kind::FLOATINGPOINT_COMPONENT_NAN, current),
	   nm->mkNode(kind::FLOATINGPOINT_COMPONENT_INF, current),
	   nm->mkNode(kind::FLOATINGPOINT_COMPONENT_ZERO, current),
	   nm->mkNode(kind::FLOATINGPOINT_COMPONENT_SIGN, current),
	   nm->mkNode(kind::FLOATINGPOINT_COMPONENT_EXPONENT, current),
	   nm->mkNode(kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND, current));

    additionalAssertions.push_back(tmp.valid(fpt(current.getType())).getNode());

    return tmp;
  }





  // Non-convertible things should only be added to the stack at the very start, thus...
  #define PASSTHROUGH   Assert(workStack.empty())


  Node fpConverter::convert (TNode node) {
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
	      f.insert(current, buildComponents(current));
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
	    case kind::FLOATINGPOINT_RTI :
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
		case kind::FLOATINGPOINT_RTI :
		  f.insert(current, symfpu::roundToIntegral<traits>(fpt(current.getType()),
								    (*mode).second,
								    (*arg1).second));
		  break;
		default :
		  Unreachable("Unknown unary rounded floating-point function");
		  break;
		}
	      }
	      break;

	    case kind::FLOATINGPOINT_REM :
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

		f.insert(current, symfpu::remainder<traits>(fpt(current.getType()),
							    (*arg1).second,
							    (*arg2).second));
	      }
	      break;

	    case kind::FLOATINGPOINT_MIN_TOTAL :
	    case kind::FLOATINGPOINT_MAX_TOTAL :
	      {
		fpMap::const_iterator arg1(f.find(current[0]));
		fpMap::const_iterator arg2(f.find(current[1]));
		// Should not need to recurse down this argument
		//ubvMap::const_iterator arg3(u.find(current[2]));

		bool recurseNeeded = (arg1 == f.end()) || (arg2 == f.end());

		if (recurseNeeded) {
		  workStack.push(current);
		  if (arg1 == f.end()) { workStack.push(current[0]); }
		  if (arg2 == f.end()) { workStack.push(current[1]); }
		  continue;    // i.e. recurse!
		}

		switch (current.getKind()) {
		case kind::FLOATINGPOINT_MAX_TOTAL :
		  f.insert(current, symfpu::max<traits>(fpt(current.getType()),
							(*arg1).second,
							(*arg2).second,
							prop(current[2])));
		  break;
		  
		case kind::FLOATINGPOINT_MIN_TOTAL :
		  f.insert(current, symfpu::min<traits>(fpt(current.getType()),
							(*arg1).second,
							(*arg2).second,
							prop(current[2])));
		  break;

		default :
		  Unreachable("Unknown binary floating-point partial function");
		  break;
		}
	      }
	      break;
	      
	    case kind::FLOATINGPOINT_PLUS :
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
		case kind::FLOATINGPOINT_REM :
		  /*
		  f.insert(current, symfpu::remainder<traits>(fpt(current.getType()),
							     (*mode).second,
							     (*arg1).second,
							     (*arg2).second));
		  */
		  Unimplemented("Remainder with rounding mode not yet supported by SMT-LIB");
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
	      {
	      Node IEEEBV(NodeManager::currentNM()->mkNode(kind::BITVECTOR_CONCAT,
							   current[0],
							   current[1],
							   current[2]));
	      f.insert(current, symfpu::unpack<traits>(fpt(current.getType()),
						       IEEEBV));
	      }
	      break;
	      
	    case kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR :
	      f.insert(current, symfpu::unpack<traits>(fpt(current.getType()),
						       ubv(current[0])));
	      break;
	      
	    case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR :
	    case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR :
	      {
		rmMap::const_iterator mode(r.find(current[0]));
		bool recurseNeeded = (mode == r.end());

		if (recurseNeeded) {
		  workStack.push(current);
		  if (mode == r.end()) { workStack.push(current[0]); }
		  continue;    // i.e. recurse!
		}

		switch (current.getKind()) {
		case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR :
		  f.insert(current, symfpu::convertSBVToFloat<traits>(fpt(current.getType()),
								      (*mode).second,
								      sbv(current[1])));
		  break;
		  
		case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR :
		  f.insert(current, symfpu::convertUBVToFloat<traits>(fpt(current.getType()),
								      (*mode).second,
								      ubv(current[1])));
		  break;

		default :
		  Unreachable("Unknown converstion from bit-vector to floating-point");
		  break;
		}
	      }
	      break;

	    case kind::FLOATINGPOINT_TO_FP_REAL :
	      {
		f.insert(current, buildComponents(current));
		// Rely on the real theory and theory combination
		// to handle the value
	      }
	      break;

	    case kind::FLOATINGPOINT_SUB :
	      Unreachable("Floating-point subtraction should be removed by the rewriter.");
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
	case kind::FLOATINGPOINT_TO_UBV_TOTAL :
	  {
	    TypeNode childType (current[1].getType());
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

	      FloatingPointToUBVTotal info =
		current.getOperator().getConst<FloatingPointToUBVTotal>();


	      u.insert(current, symfpu::convertFloatToUBV<traits>(fpt(childType),
								  (*mode).second,
								  (*arg1).second,
								  info.bvs,
								  ubv(current[2])));
	      i = u.find(current);
	    }
	      
	    result = (*i).second.getNode();
	  }
	  break;

	case kind::FLOATINGPOINT_TO_SBV_TOTAL :
	  {
	    TypeNode childType (current[1].getType());
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

	      FloatingPointToSBVTotal info =
		current.getOperator().getConst<FloatingPointToSBVTotal>();


	      s.insert(current, symfpu::convertFloatToSBV<traits>(fpt(childType),
								  (*mode).second,
								  (*arg1).second,
								  info.bvs,
								  sbv(current[2])));

	      i = s.find(current);
	    }

	    result = (*i).second.getNode();
	  }
	  break;

	case kind::FLOATINGPOINT_TO_UBV :
	  Unreachable("Partially defined fp.to_ubv should have been removed by expandDefinition");
	  break;

	case kind::FLOATINGPOINT_TO_SBV :
	  Unreachable("Partially defined fp.to_sbv should have been removed by expandDefinition");
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
	case kind::FLOATINGPOINT_TO_REAL_TOTAL :
	  {
	    // We need to recurse so that any variables that are only
	    // used under this will have components created
	    // (via auxiliary constraints)

	    TypeNode childType (current[0].getType());
	    fpMap::const_iterator arg1(f.find(current[0]));

	    if (arg1 == f.end()) {
	      workStack.push(current);
	      workStack.push(current[0]);
	      continue;    // i.e. recurse!
	    }

	    // However we don't need to do anything explicitly with
	    // this as it will be treated as an uninterpreted function
	    // by the real theory and we don't need to bit-blast the
	    // float expression unless we need to say something about
	    // its value.
	  }

	  break;

	case kind::FLOATINGPOINT_TO_REAL :
	  Unreachable("Partially defined fp.to_real should have been removed by expandDefinition");
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
    Assert(Theory::isLeafOf(var, THEORY_FP));

    TypeNode t(var.getType());

#ifdef REMOVE
    NodeManager *nm = NodeManager::currentNM();
#endif

    if (t.isRoundingMode()) {
      rmMap::const_iterator i(r.find(var));

      if (i == r.end()) {
	Unreachable("Asking for the value of an unregistered expression");
      } else {
	Node value = rmToNode((*i).second);
	return value;
      }

#ifdef REMOVE
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
#endif

    } else if (t.isFloatingPoint()) {

      fpMap::const_iterator i(f.find(var));
      
      if (i == f.end()) {
	Unreachable("Asking for the value of an unregistered expression");
      } else {

	Node value = ufToNode(fpt(t), (*i).second);
	return value;

#ifdef REMOVE
	Node nanValue = val.getModelValue((*i).second.nan.getNode());
	Assert(nanValue.isConst());
	#ifdef SYMFPUPROPISBOOL
	Assert(nanValue.getType().isBoolean());
	#else
	Assert(nanValue.getType().isBitVector());	
	Assert(nanValue.getType().getBitVectorSize() == 1);
	#endif

	Node infValue = val.getModelValue((*i).second.inf.getNode());
	Assert(infValue.isConst());
	#ifdef SYMFPUPROPISBOOL
	Assert(infValue.getType().isBoolean());
	#else
	Assert(infValue.getType().isBitVector());	
	Assert(infValue.getType().getBitVectorSize() == 1);
	#endif

	Node zeroValue = val.getModelValue((*i).second.zero.getNode());
	Assert(zeroValue.isConst());
	#ifdef SYMFPUPROPISBOOL
	Assert(zeroValue.getType().isBoolean());
        #else
	Assert(zeroValue.getType().isBitVector());	
	Assert(zeroValue.getType().getBitVectorSize() == 1);
	#endif

	Node signValue = val.getModelValue((*i).second.sign.getNode());
	Assert(signValue.isConst());
	#ifdef SYMFPUPROPISBOOL
	Assert(signValue.getType().isBoolean());
	#else
	Assert(signValue.getType().isBitVector());	
	Assert(signValue.getType().getBitVectorSize() == 1);
	#endif

	Node exponentValue = val.getModelValue((*i).second.exponent.getNode());
	Assert(exponentValue.isConst());
	Assert(exponentValue.getType().isBitVector());

	Node significandValue = val.getModelValue((*i).second.significand.getNode());
	Assert(significandValue.isConst());
	Assert(significandValue.getType().isBitVector());


	#ifdef SYMFPUPROPISBOOL
	#else
	Node trueBit = NodeManager::currentNM()->mkConst(BitVector(1U,1U));
	#endif

	FloatingPointLiteral fpl(
				 #ifdef SYMFPUPROPISBOOL
				 nanValue.getConst<bool>(),
				 infValue.getConst<bool>(),
				 zeroValue.getConst<bool>(),
				 signValue.getConst<bool>(),
				 #else
				 nanValue == trueBit,
				 infValue == trueBit,
				 zeroValue == trueBit,
				 signValue == trueBit,
				 #endif
				 exponentValue.getConst<BitVector>(),
				 significandValue.getConst<BitVector>());
	return NodeManager::currentNM()->mkConst(FloatingPoint(var.getType().getConst<FloatingPointSize>(), fpl));
#endif
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
