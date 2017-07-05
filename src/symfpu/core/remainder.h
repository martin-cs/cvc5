/*
** Copyright (C) 2017 Martin Brain
** 
** This program is free software: you can redistribute it and/or modify
** it under the terms of the GNU General Public License as published by
** the Free Software Foundation, either version 3 of the License, or
** (at your option) any later version.
** 
** This program is distributed in the hope that it will be useful,
** but WITHOUT ANY WARRANTY; without even the implied warranty of
** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
** GNU General Public License for more details.
** 
** You should have received a copy of the GNU General Public License
** along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

/*
** remainder.h
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 14/12/16
**
** Computing the IEEE-754 remainder of arbitrary precision floats
**
*/

#include "symfpu/core/unpackedFloat.h"
#include "symfpu/core/ite.h"
#include "symfpu/core/rounder.h"
#include "symfpu/core/operations.h"

#ifndef SYMFPU_REMAINDER
#define SYMFPU_REMAINDER

namespace symfpu {

template <class t>
  unpackedFloat<t> addRemainderSpecialCases (const typename t::fpt &format,
					    const unpackedFloat<t> &left,
					    const unpackedFloat<t> &right,
					    const unpackedFloat<t> &remainderResult) {
  typedef typename t::prop prop;

  prop eitherArgumentNan(left.getNaN() || right.getNaN());
  prop generateNan(left.getInf() || right.getZero());
  prop isNan(eitherArgumentNan || generateNan);

  prop passThrough(!(left.getInf() || left.getNaN()) && right.getInf());

  return ITE(isNan,
	     unpackedFloat<t>::makeNaN(format),
	     ITE(passThrough,
		 left,
		 remainderResult));
 }

template <class t>
  unpackedFloat<t> arithmeticRemainder (const typename t::fpt &format,
					const typename t::rm &roundingMode,
					const unpackedFloat<t> &left,
					const unpackedFloat<t> &right) {
  typedef typename t::bwt bwt;
  typedef typename t::prop prop;
  typedef typename t::ubv ubv;
  typedef typename t::sbv sbv;
  typedef typename t::fpt fpt;

  PRECONDITION(left.valid(format));
  PRECONDITION(right.valid(format));

  // Compute sign
  prop remainderSign(left.getSign());


  #if 0
  
  // Add up exponents
  sbv exponentSum(expandingAdd<t>(left.getExponent(),right.getExponent()));
  // Optimisation : do this late and use the increment as a carry in

  sbv min(unpackedFloat<t>::minSubnormalExponent(format));
  sbv max(unpackedFloat<t>::maxNormalExponent(format));
  INVARIANT(expandingAdd<t>(min,min) <= exponentSum);
  INVARIANT(exponentSum <= expandingAdd<t>(max, max));
  // Optimisation : use the if-then-lazy-else to avoid remaindering for underflow and overflow
  //                subnormal * subnormal does not need to be evaluated


  // Remainder the significands
  ubv significandProduct(expandingRemainder<t>(left.getSignificand(), right.getSignificand()));
  // Optimisation : low bits are not needed apart from the guard and sticky bits
  // Optimisation : top bits accurately predict whether re-alignment is needed

  bwt spWidth(significandProduct.getWidth());
  ubv topBit(significandProduct.extract(spWidth - 1, spWidth - 1));
  ubv nextBit(significandProduct.extract(spWidth - 2, spWidth - 2));

  // Alignment of inputs means at least one of the two MSB is 1
  //  i.e. [1,2) * [1,2) = [1,4)
  // topBitSet is the likely case
  prop topBitSet(topBit.isAllOnes());
  INVARIANT(topBitSet || nextBit.isAllOnes());
  probabilityAnnotation<t>(topBitSet, LIKELY);
  

  // Re-align
  sbv alignedExponent(conditionalIncrement<t>(topBitSet, exponentSum)); // Will not overflow as previously expanded
  ubv alignedSignificand(conditionalLeftShiftOne<t>(!topBitSet, significandProduct)); // Will not loose information

  
  // Put back together
  unpackedFloat<t> remainderResult(remainderSign, alignedExponent, alignedSignificand);

  
  fpt extendedFormat(format.exponentWidth() + 1, format.significandWidth() * 2);
  POSTCONDITION(remainderResult.valid(extendedFormat));

  return remainderResult;
#endif

  // TODO : wrong!
  return left;
 }


// Put it all together...
template <class t>
  unpackedFloat<t> remainder (const typename t::fpt &format,
			     const typename t::rm &roundingMode,
			     const unpackedFloat<t> &left,
			     const unpackedFloat<t> &right) {
  //typedef typename t::bwt bwt;
  //typedef typename t::prop prop;
  //typedef typename t::ubv ubv;
  //typedef typename t::sbv sbv;

  PRECONDITION(left.valid(format));
  PRECONDITION(right.valid(format));

  unpackedFloat<t> remainderResult(arithmeticRemainder(format, roundingMode, left, right));
  
  //unpackedFloat<t> result(addRemainderSpecialCases(format, left, right, roundedRemainderResult));
  unpackedFloat<t> result(addRemainderSpecialCases(format, left, right, remainderResult));

  POSTCONDITION(result.valid(format));

  return result;
 }


}

#endif

