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
#include "symfpu/core/packing.h"
#include "symfpu/core/compare.h"
#include "symfpu/core/sign.h"
#include "symfpu/core/classify.h"
#include "symfpu/core/add.h"
#include "symfpu/core/multiply.h"
#include "symfpu/core/fma.h"
#include "symfpu/core/divide.h"
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

  BitVector FloatingPoint::pack (void) const {
    BitVector bv(symfpu::pack<symfpuLiteral::traits>(this->t, this->fpl));
    return bv;
  }



}/* CVC4 namespace */
