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
** add.h
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 01/09/14
**
** Addition of arbitrary precision floats
**
*/

#include "symfpu/core/unpackedFloat.h"
#include "symfpu/core/ite.h"
#include "symfpu/core/rounder.h"
#include "symfpu/core/sign.h"

#ifndef SYMFPU_ADD
#define SYMFPU_ADD

namespace symfpu {

template <class t>
  unpackedFloat<t> addAdditionSpecialCases (const typename t::fpt &format,
					    const typename t::rm &roundingMode,
					    const unpackedFloat<t> &left,
					    const unpackedFloat<t> &right,
					    const unpackedFloat<t> &additionResult,
					    const typename t::prop &isAdd) {
  typedef typename t::prop prop;

  // NaN
  prop eitherArgumentNan(left.getNan() || right.getNan());
  prop bothInfinity(left.getInf() && right.getInf());
  prop signsMatch(left.getSign() == right.getSign());
  //prop compatableSigns(ITE(isAdd, signsMatch, !signsMatch));
  prop compatableSigns(isAdd ^ !signsMatch);

  prop generatesNaN(eitherArgumentNan || (bothInfinity && !compatableSigns));


  // Inf
  prop generatesInf((bothInfinity && compatableSigns) ||
		    ( left.getInf() && !right.getInf()) ||
		    (!left.getInf() &&  right.getInf()));

  prop signOfInf(ITE(left.getInf(), left.getSign(), prop(isAdd ^ !right.getSign())));

  
  // Zero
  prop bothZero(left.getZero() && right.getZero());
  prop flipRightSign(!isAdd ^ right.getSign());
  prop signOfZero(ITE((roundingMode == t::RTN()),
		      left.getSign() || flipRightSign,
		      left.getSign() && flipRightSign));

  prop  idLeft(!left.getZero() &&  right.getZero());
  prop idRight( left.getZero() && !right.getZero());

  return ITE(generatesNaN,
	     unpackedFloat<t>::makeNaN(format),
	     ITE(generatesInf,
		 unpackedFloat<t>::makeInf(format, signOfInf),
		 ITE(bothZero,
		     unpackedFloat<t>::makeZero(format, signOfZero),
		     ITE(idLeft,
			 left,
			 ITE(idRight,
			     ITE(isAdd,
				 right,
				 negate(format, right)),
			     additionResult)))));
 }
 

  /*
   * 1. Compute the normal / subnormal case.
   * 2. Round to the format.
   * 3. Then have a function that takes the uf generated and adds the
   *    other conditions.
   *
   * This allows multiple versions of the first phase to be used and
   * the first phase to be used for other things (e.g. FMA).
   */

 template <class t>
   unpackedFloat<t> add (const typename t::fpt &format,
			 const typename t::rm &roundingMode,
			 const unpackedFloat<t> &left,
			 const unpackedFloat<t> &right,
			 const typename t::prop &isAdd) {
   // Optimisation : add a flag which assumes that left and right are in exponent order
   
   typedef typename t::bwt bwt;
   typedef typename t::prop prop;
   typedef typename t::ubv ubv;
   typedef typename t::sbv sbv;
   
   PRECONDITION(left.valid(format));
   PRECONDITION(right.valid(format));


   // Compute exponent difference and swap the two arguments if needed
   sbv initialExponentDifference(left.getExponent().expandingSubtract(right.getExponent()));
   bwt edWidth(initialExponentDifference.getWidth());
   sbv edWidthZero(sbv::zero(edWidth));
   prop orderingCorrect( initialExponentDifference >  edWidthZero ||
			(initialExponentDifference == edWidthZero &&
			 left.getSignificand() >= right.getSignificand()));

   unpackedFloat<t> larger(ITE(orderingCorrect, left, right));
   unpackedFloat<t> smaller(ITE(orderingCorrect, right, left));
   sbv exponentDifference(ITE(orderingCorrect,
			      initialExponentDifference,
			      -initialExponentDifference));

   prop resultSign(ITE(orderingCorrect,
		       left.getSign(),
		       prop(!isAdd ^ right.getSign())));


   // Work out if an effective subtraction
   prop effectiveAdd(larger.getSign() ^ smaller.getSign() ^ isAdd);

   
   // Extend the significands to give room for carry plus guard and sticky bits
   ubv lsig( larger.getSignificand().extend(1).append(ubv::zero(2)));
   ubv ssig(smaller.getSignificand().extend(1).append(ubv::zero(2)));


   // This is a two-path adder, so determine which of the two paths to use 
   // The near path is only needed for things that can cancel more than one bit
   prop farPath(exponentDifference > sbv::one(edWidth) || effectiveAdd);


   // Far path : Align
   ubv negatedSmaller(ITE(effectiveAdd, ssig, ssig.modularNegate())); // Extended so no info lost
                                                                      // Negate before shift so that sign-extension works

   sbv significandWidth(edWidth, lsig.getWidth());
   prop noOverlap(exponentDifference > significandWidth);

   ubv shiftAmount(exponentDifference.toUnsigned() // Safe as >= 0
		   .resize(ssig.getWidth()));      // This looses information but the case in which it does is handles by noOverlap


   ubv negatedAlignedSmaller(negatedSmaller.signExtendRightShift(shiftAmount));
   ubv shiftedStickyBit(negatedSmaller.rightShiftStickyBit(shiftAmount));  // Have to separate otherwise align up may convert it to the guard bit

   // Far path : Sum and re-align
   ubv sum(lsig.modularAdd(negatedAlignedSmaller));

   bwt sumWidth(sum.getWidth());
   ubv topBit(sum.extract(sumWidth - 1, sumWidth - 1));
   ubv centerBit(sum.extract(sumWidth - 2, sumWidth - 2));

   prop noOverflow(topBit.isAllZeros()); // Only correct if effectiveAdd is set
   prop noCancel(centerBit.isAllOnes());

   // TODO : Add invariants

   ubv alignedSum(ITE(effectiveAdd,
		      ITE(noOverflow,
			  sum,
			  (sum >> 1) | (sum & ubv::one(sumWidth))),  // Cheap sticky right shift
		      ITE(noCancel,
			  sum,
			  sum.modularLeftShift(1)))); // In the case when this looses data, the result is not used

   sbv extendedLargerExponent(larger.getExponent().extend(1));  // So that increment and decrement don't overflow
   sbv correctedExponent(ITE(effectiveAdd,
			     ITE(noOverflow,
				 extendedLargerExponent,
				 extendedLargerExponent.increment()),
			     ITE(noCancel,
				 extendedLargerExponent,
				 extendedLargerExponent.decrement())));

   // Far path : Round
   unpackedFloat<t> farPathResult(resultSign, correctedExponent, (alignedSum | shiftedStickyBit).contract(1));
   unpackedFloat<t> roundedFarPathResult(rounder(format, roundingMode, farPathResult));



   // Near path : Align
   prop exponentDifferenceAllZeros(exponentDifference.isAllZeros());
   ubv nearAlignedSmaller(ITE(exponentDifferenceAllZeros, ssig, ssig >> 1));


   // Near path : Sum and realign
   ubv nearSum(lsig - nearAlignedSmaller);
   // Optimisation : the two paths can be merged up to here to give a pseudo-two path encoding

   prop fullCancel(nearSum.isAllZeros());
   prop nearNoCancel(nearSum.extract(sumWidth - 2, sumWidth - 2).isAllOnes());

   ubv choppedNearSum(nearSum.extract(sumWidth - 3,1)); // In the case this is used, cut bits are all 0 
   unpackedFloat<t> cancellation(resultSign, 
				 larger.getExponent().decrement(),
				 choppedNearSum);


   // Near path : Round
   // Optimisation : share the rounder with the far path, or specialise
   unpackedFloat<t> nearPathResult(resultSign, extendedLargerExponent, nearSum.contract(1));
   unpackedFloat<t> roundedNearPathResult(rounder(format, roundingMode, nearPathResult));





   // Bring the paths together
   // Optimisation : fix the noOverlap / very far path for directed rounding modes
   unpackedFloat<t> additionResult(ITE(farPath,
				       /* ITE(noOverlap,
					   ITE((isAdd || orderingCorrect),
					       larger,
					       negate(format, larger)),
					       roundedFarPathResult), */
				       roundedFarPathResult,
				       ITE(fullCancel,
					   unpackedFloat<t>::makeZero(format, roundingMode == t::RTN()),
					   ITE(nearNoCancel,
					       roundedNearPathResult,
					       cancellation.normaliseUp(format)))));
   unpackedFloat<t> result(addAdditionSpecialCases(format, roundingMode, left, right, additionResult, isAdd));
   
   POSTCONDITION(result.valid(format));
   
   return result;
 }


}

#endif

