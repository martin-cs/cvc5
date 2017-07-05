/*********************                                                        */
/*! \file floatingpoint.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Martin Brain
 ** Copyright (c) 2013  University of Oxford
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Implementations of the utility functions for working with floating point theories. ]]
 **
 **/

#include <math.h>

#include "base/cvc4_assert.h"
#include "util/floatingpoint.h"
#include "util/integer.h"
#include "symfpu/core/packing.h"
#include "symfpu/core/compare.h"
#include "symfpu/core/sign.h"
#include "symfpu/core/classify.h"
#include "symfpu/core/add.h"
#include "symfpu/core/multiply.h"
#include "symfpu/core/fma.h"
#include "symfpu/core/divide.h"
#include "symfpu/core/sqrt.h"
#include "symfpu/core/convert.h"


namespace CVC4 {

FloatingPointSize::FloatingPointSize (unsigned _e, unsigned _s) : e(_e), s(_s)
{
  PrettyCheckArgument(validExponentSize(_e),_e,"Invalid exponent size : %d",_e);
  PrettyCheckArgument(validSignificandSize(_s),_s,"Invalid significand size : %d",_s);
}

FloatingPointSize::FloatingPointSize (const FloatingPointSize &old) : e(old.e), s(old.s)
{
  PrettyCheckArgument(validExponentSize(e),e,"Invalid exponent size : %d",e);
  PrettyCheckArgument(validSignificandSize(s),s,"Invalid significand size : %d",s);
}

#if 0
  /* symfpu requires that all types that it manages are correctly
   * constructed.  This means that structures that contain them have
   * to initialise them via constructor which is rather limited.  So
   * we have to have helper methods and then use the copy constructor...
   */

  static FloatingPointLiteral constructorHelperLiteral (unsigned e, unsigned s, double d) {

    switch (fpclassify(d)) {
    case FP_NAN : return symfpuLiteral::uf::makeNaN(symfpuLiteral::fpt(e,s));
      break;
    case FP_INFINITE : return symfpuLiteral::uf::makeInf(symfpuLiteral::fpt(e,s), signbit(d));
      break;
    case FP_ZERO : return symfpuLiteral::uf::makeZero(symfpuLiteral::fpt(e,s), signbit(d));
      break;
    case FP_SUBNORMAL :
    case FP_NORMAL :
      // Only used for special values so ...
    default :
    Unimplemented("Not done yet!");
    }
  }

  FloatingPoint::FloatingPoint (unsigned e, unsigned s, double d) : fpl(constructorHelperLiteral(e,s,d)), t(e,s) {}

  static FloatingPointLiteral constructorHelperString (unsigned e, unsigned s, const std::string &bitString) {
    Unimplemented("Not done yet!");
  }

  FloatingPoint::FloatingPoint (unsigned e, unsigned s, const std::string &bitString) : fpl(constructorHelperString(e,s,bitString)), t(e,s) {}
#endif


  FloatingPoint::FloatingPoint (unsigned e, unsigned s, const BitVector &bv) :
    fpl(symfpu::unpack<symfpuLiteral::traits>(symfpuLiteral::fpt(e,s), bv)),
    t(e,s) {}


  static FloatingPointLiteral constructorHelperBitVector (const FloatingPointSize &ct, const RoundingMode &rm, const BitVector &bv, bool signedBV) {
    if (signedBV) {
      return FloatingPointLiteral(symfpu::convertSBVToFloat<symfpuLiteral::traits>(symfpuLiteral::fpt(ct),
										   symfpuLiteral::rm(rm),
										   symfpuLiteral::sbv(bv)));
    } else {
      return FloatingPointLiteral(symfpu::convertUBVToFloat<symfpuLiteral::traits>(symfpuLiteral::fpt(ct),
										   symfpuLiteral::rm(rm),
										   symfpuLiteral::ubv(bv)));
    }
    Unreachable("Constructor helper broken");
  }
  
  FloatingPoint::FloatingPoint (const FloatingPointSize &ct, const RoundingMode &rm, const BitVector &bv, bool signedBV) :
    fpl(constructorHelperBitVector(ct, rm, bv, signedBV)),
    t(ct) {}

  
  static FloatingPointLiteral constructorHelperRational (const FloatingPointSize &ct, const RoundingMode &rm, const Rational &ri) {
    Rational r(ri);
    Rational two(2,1);
    
    if (r.isZero()) {
      return FloatingPointLiteral::makeZero(ct, false); // In keeping with the SMT-LIB standard
    } else {
      int negative = (r.sgn() < 0) ? 1 : 0;
      r.abs();

      // Compute the exponent
      Integer exp(0U);
      Integer inc(1U);
      Rational working(1,1);

      if (r == working) {

      } else if ( r < working ) {
	while (r < working) {
	  exp -= inc;
	  working /= two;
	}
	exp += inc;
	working *= two;
	
      } else {
	while (r > working) {
	  exp += inc;
	  working *= two;
	}
	exp -= inc;
	working /= two;
      }

      Assert(working <= r);
      Assert(r < working * two);

      // Work out the number of bits required to represent the exponent
      unsigned expBits = 2; // No point starting with an invalid amount

      Integer doubleInt(2);
      if (exp.strictlyPositive()) {
	Integer representable(4);
	while (representable < exp) {
	  representable *= doubleInt;
	  ++expBits;
	}
      } else if (exp.strictlyNegative()) {
	Integer representable(-4);
	while (representable > exp) {
	  representable *= doubleInt;
	  ++expBits;
	}
      }
      ++expBits; // To allow for sign

      BitVector exactExp(expBits, exp);

      
      
      // Compute the significand.
      unsigned sigBits = ct.significandWidth() + 2; // guard and sticky bits
      BitVector sig(sigBits, 0U);
      BitVector one(sigBits, 1U);
      Rational workingSig(0,1);
      for (unsigned i = 0; i < sigBits - 1; ++i) {
	Rational mid(workingSig + working);

	if (mid < r) {
	  sig = sig | one;
	  workingSig = mid;
	}

	sig = sig.leftShift(one);
	working /= two;
      }

      // Compute the sticky bit
      Rational remainder(r - workingSig);
      Assert(Rational(0,1) <= remainder);

      if (!remainder.isZero()) {
	sig = sig | one;
      }

      // Build an exact float
      FloatingPointSize exactFormat(expBits, sigBits);
      FloatingPointLiteral exactFloat(negative, exactExp, sig);
      

      // Then cast...
      FloatingPointLiteral rounded(symfpu::convertFloatToFloat(exactFormat,
							       ct,
							       rm,
							       exactFloat));
      return rounded;
    }
    Unreachable("Constructor helper broken");
  }
  
  FloatingPoint::FloatingPoint (const FloatingPointSize &ct, const RoundingMode &rm, const Rational &r) :
    fpl(constructorHelperRational(ct, rm, r)),
    t(ct) {}

  
  FloatingPoint FloatingPoint::makeNaN (const FloatingPointSize &t) {
    return FloatingPoint(t, symfpu::unpackedFloat<symfpuLiteral::traits>::makeNaN(t));
  }

  FloatingPoint FloatingPoint::makeInf (const FloatingPointSize &t, bool sign) {
    return FloatingPoint(t, symfpu::unpackedFloat<symfpuLiteral::traits>::makeInf(t, sign));
  }

  FloatingPoint FloatingPoint::makeZero (const FloatingPointSize &t, bool sign) {
    return FloatingPoint(t, symfpu::unpackedFloat<symfpuLiteral::traits>::makeZero(t, sign));
  }


  /* Operations implemented using symfpu */
  FloatingPoint FloatingPoint::absolute (void) const {
    return FloatingPoint(t, symfpu::absolute<symfpuLiteral::traits>(t, fpl));
  }
  
  FloatingPoint FloatingPoint::negate (void) const {
    return FloatingPoint(t, symfpu::negate<symfpuLiteral::traits>(t, fpl));
  }
  
  FloatingPoint FloatingPoint::plus (const RoundingMode &rm, const FloatingPoint &arg) const {
    Assert(this->t == arg.t);
    return FloatingPoint(t, symfpu::add<symfpuLiteral::traits>(t, rm, fpl, arg.fpl, true));
  }

  FloatingPoint FloatingPoint::sub (const RoundingMode &rm, const FloatingPoint &arg) const {
    Assert(this->t == arg.t);
    return FloatingPoint(t, symfpu::add<symfpuLiteral::traits>(t, rm, fpl, arg.fpl, false));
  }

  FloatingPoint FloatingPoint::mult (const RoundingMode &rm, const FloatingPoint &arg) const {
    Assert(this->t == arg.t);
    return FloatingPoint(t, symfpu::multiply<symfpuLiteral::traits>(t, rm, fpl, arg.fpl));
  }

  FloatingPoint FloatingPoint::fma (const RoundingMode &rm, const FloatingPoint &arg1, const FloatingPoint &arg2) const {
    Assert(this->t == arg1.t);
    Assert(this->t == arg2.t);
    return FloatingPoint(t, symfpu::fma<symfpuLiteral::traits>(t, rm, fpl, arg1.fpl, arg2.fpl));
  }

  FloatingPoint FloatingPoint::div (const RoundingMode &rm, const FloatingPoint &arg) const {
    Assert(this->t == arg.t);
    return FloatingPoint(t, symfpu::divide<symfpuLiteral::traits>(t, rm, fpl, arg.fpl));
  }

  FloatingPoint FloatingPoint::sqrt (const RoundingMode &rm) const {
    return FloatingPoint(t, symfpu::sqrt<symfpuLiteral::traits>(t, rm, fpl));
  }

  FloatingPoint FloatingPoint::rti (const RoundingMode &rm) const {
    return FloatingPoint(t, symfpu::roundToIntegral<symfpuLiteral::traits>(t, rm, fpl));
  }

  FloatingPoint FloatingPoint::rem (const RoundingMode &rm, const FloatingPoint &arg) const {
    Assert(this->t == arg.t);
    Unimplemented("Remainder not implemented in symfpu");
    //return FloatingPoint(t, symfpu::remainder<symfpuLiteral::traits>(t, rm, fpl, arg.fpl));
    return *this;
  }

  FloatingPoint FloatingPoint::max (const FloatingPoint &arg, bool zeroCaseLeft) const {
    Assert(this->t == arg.t);
    return FloatingPoint(t, symfpu::max<symfpuLiteral::traits>(t, fpl, arg.fpl));//, zeroCaseLeft));
  }
  
  FloatingPoint FloatingPoint::min (const FloatingPoint &arg, bool zeroCaseRight) const {
    Assert(this->t == arg.t);
    return FloatingPoint(t, symfpu::min<symfpuLiteral::traits>(t, fpl, arg.fpl));//, zeroCaseLeft));
  }

  bool FloatingPoint::operator ==(const FloatingPoint& fp) const {
    return ( (t == fp.t) && symfpu::smtlibEqual<symfpuLiteral::traits>(t,fpl,fp.fpl) );
  }

  bool FloatingPoint::operator <= (const FloatingPoint &arg) const {
    Assert(this->t == arg.t);
    return symfpu::lessThanOrEqual<symfpuLiteral::traits>(t, fpl, arg.fpl);
  }

  bool FloatingPoint::operator < (const FloatingPoint &arg) const {
    Assert(this->t == arg.t);
    return symfpu::lessThan<symfpuLiteral::traits>(t, fpl, arg.fpl);
  }

  bool FloatingPoint::isNormal (void) const {
    return symfpu::isNormal<symfpuLiteral::traits>(t, fpl);
  }

  bool FloatingPoint::isSubnormal (void) const {
    return symfpu::isSubnormal<symfpuLiteral::traits>(t, fpl);
  }

  bool FloatingPoint::isZero (void) const {
    return symfpu::isZero<symfpuLiteral::traits>(t, fpl);
  }

  bool FloatingPoint::isInfinite (void) const {
    return symfpu::isInfinite<symfpuLiteral::traits>(t, fpl);
  }

  bool FloatingPoint::isNaN (void) const {
    return symfpu::isNaN<symfpuLiteral::traits>(t, fpl);
  }

  bool FloatingPoint::isNegative (void) const {
    return symfpu::isNegative<symfpuLiteral::traits>(t, fpl);
  }

  bool FloatingPoint::isPositive (void) const {
    return symfpu::isPositive<symfpuLiteral::traits>(t, fpl);
  }

  FloatingPoint FloatingPoint::convert (const FloatingPointSize &target, const RoundingMode &rm) const {
    return FloatingPoint(target, symfpu::convertFloatToFloat<symfpuLiteral::traits>(t, target, rm, fpl));
  }
  
  BitVector FloatingPoint::convertToBV (BitVectorSize width, const RoundingMode &rm, bool signedBV) const {
    if (signedBV)
      return symfpu::convertFloatToSBV<symfpuLiteral::traits>(t, rm, fpl, width, BitVector(width, 0U));
    else
      return symfpu::convertFloatToUBV<symfpuLiteral::traits>(t, rm, fpl, width, BitVector(width, 0U));
  }

  Rational FloatingPoint::convertToRational (void) const {
    // Is the internal semantics -- ignores NaN and Inf

    if (this->isZero()) {
      return Rational(0U, 1U);
      
    } else {

      Integer sign((this->fpl.getSign()) ? -1 : 1); 
      Integer exp(this->fpl.getExponent().toInteger() - Integer(t.significand()));
      Integer significand(this->fpl.getSignificand().toInteger());
      Integer signedSignificand(sign * significand);
      
      // Only have pow(uint32_t) so we should check this.
      Assert(this->t.significand() <= 32);
      
      if (!(exp.strictlyNegative())) {
	Integer r(signedSignificand.multiplyByPow2(exp.toUnsignedInt()));
	return Rational(r);
      } else {
	Integer one(1U);
	Integer q(one.multiplyByPow2((-exp).toUnsignedInt()));
	Rational r(signedSignificand, q);
	return r;
      }
    }

    Unreachable("Convert float literal to real broken.");
  }

  BitVector FloatingPoint::pack (void) const {
    BitVector bv(symfpu::pack<symfpuLiteral::traits>(this->t, this->fpl));
    return bv;
  }



}/* CVC4 namespace */
