/*
** Copyright (C) 2015 Martin Brain
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
** multiply.h
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 25/08/14
**
** Multiplication of arbitrary precision floats
**
*/

#include "symfpu/core/unpackedFloat.h"
#include "symfpu/core/ite.h"
#include "symfpu/core/rounder.h"

#ifndef SYMFPU_MULTIPLY
#define SYMFPU_MULTIPLY

namespace symfpu {

template <class t>
  unpackedFloat<t> addMultiplySpecialCases (const typename t::fpt &format,
					    const unpackedFloat<t> &left,
					    const unpackedFloat<t> &right,
					    const unpackedFloat<t> &multiplyResult) {
  typedef typename t::prop prop;

  prop eitherArgumentNan(left.getNaN() || right.getNaN());
  prop generateNan((left.getInf() && right.getZero()) ||
		   (left.getZero() && right.getInf()));
  prop isNan(eitherArgumentNan || generateNan);

  prop isInf(left.getInf() || right.getInf());

  prop isZero(left.getZero() || right.getZero());

  return ITE(isNan,
	     unpackedFloat<t>::makeNaN(format),
	     ITE(isInf,
		 unpackedFloat<t>::makeInf(format, multiplyResult.getSign()),
		 ITE(isZero,
		     unpackedFloat<t>::makeZero(format, multiplyResult.getSign()),
		     multiplyResult)));
 }

template <class t>
  unpackedFloat<t> multiply (const typename t::fpt &format,
			     const typename t::rm &roundingMode,
			     const unpackedFloat<t> &left,
			     const unpackedFloat<t> &right) {
  typedef typename t::bwt bwt;
  typedef typename t::prop prop;
  typedef typename t::ubv ubv;
  typedef typename t::sbv sbv;

  PRECONDITION(left.valid(format));
  PRECONDITION(right.valid(format));

  // Compute sign
  prop multiplySign(left.getSign() ^ right.getSign());

  // Add up exponents
  sbv exponentSum(left.getExponent().expandingAdd(right.getExponent()));
  // Optimisation : do this late and use the increment as a carry in

  sbv min(unpackedFloat<t>::minSubnormalExponent(format));
  sbv max(unpackedFloat<t>::maxNormalExponent(format));
  INVARIANT(min.expandingAdd(min) <= exponentSum);
  INVARIANT(exponentSum <= max.expandingAdd(max));
  // Optimisation : use the if-then-lazy-else to avoid multiplying for underflow and overflow
  //                subnormal * subnormal does not need to be evaluated


  // Multiply the significands
  ubv significandProduct(left.getSignificand().expandingMultiply(right.getSignificand()));
  // Optimisation : low bits are not needed apart from the guard and sticky bits
  // Optimisation : top bits accurately predict whether re-alignment is needed

  bwt spWidth(significandProduct.getWidth());
  ubv topBit(significandProduct.extract(spWidth - 1, spWidth - 1));
  ubv nextBit(significandProduct.extract(spWidth - 2, spWidth - 2));

  // Alignment of inputs means at least one of the two MSB is 1
  // i.e. [1,2) * [1,2) = [1,4)
  prop topBitSet(topBit.isAllOnes());
  INVARIANT(topBitSet || nextBit.isAllOnes());
  

  // Re-align
  sbv incrementExponentSum(exponentSum + sbv::one(exponentSum.getWidth()));  // Will not overflow
  sbv alignedExponent(ITE(topBitSet, incrementExponentSum, exponentSum));
  
  ubv shiftedSignificandProduct(significandProduct.modularLeftShift(1));     // Will not loose information
  ubv alignedSignificand(ITE(topBitSet, significandProduct, shiftedSignificandProduct));

  
  // Put back together
  unpackedFloat<t> multiplyResult(multiplySign, alignedExponent, alignedSignificand);
  
  unpackedFloat<t> roundedMultiplyResult(rounder(format, roundingMode, multiplyResult));
  
  unpackedFloat<t> result(addMultiplySpecialCases(format, left, right, roundedMultiplyResult));

  POSTCONDITION(result.valid(format));

  return result;
 }



}

#endif

