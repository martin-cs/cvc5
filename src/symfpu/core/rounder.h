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
** rounder.h
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 26/08/14
**
** Rounding arbitrary length unpacked floats back to their correct length.
**
*/

/*
 * Rounder Ideas
 *
 *  - get the rounder to handle things with 1 or 2 possible leading
 *    0's rather than normalise before and after rounding.
 *    Subnormal rounding should ideally be temporarily denormalised to
 *    avoid the expensive variable position rounding.
 *
 *  1. Take exponent and add a 0 at the start to deal with overflow.
 *     (may not be needed if the exponent has already been extended due
 *      to subnormals, addition, etc.)
 *  2. For each of the possible positions of the binary point, produce
 *     an incremented version and round and sticky bits.
 *     (given the alignment is known, may be able to just pick how much
 *      to increment by and then increment once.)
 *  3. The leading zeros of the original exponent pick which set of
 *     round and sticky to use.  Thus pick which of the incremented /
 *     normal to use and align apart from 1.
 *  4. Finally align, most of the information needed for this will be
 *     already known.
 *
 * - can fold the increment from the rounder into the circuitry / 
 *   last round of accumulation.
 *   In fact, can take this further.  a + b + 1 takes the same
 *   circuitry as a + b.  a * b + 1 shares most of the circuit with
 *   a * b and neither of them require a sign extension.  Extending
 *   this to a + b + k and a * b + k for positional rounding is an 
 *   open question.
 *
 * - add a 'non-deterministic rounding' mode for underapproximation.
 *
 * - add a early underflow / overflow for cases that rounding does not
 *   effect.  This will allow the complex cases to be abstracted out.
 *
 * - Specialised rounders
 *    Additive
 *     Only one overflow increment is possible, even for a + b + 1
 *     When a subnormal number if generated, it is exact and thus you
 *      don't need to think about positional rounding for the
 *      subnormals.
 *     No need to check for underflow to zero for similar reasons.
 *     The rounder for the near path can be even more specialised as 
 *      the sticky bit is always 1 and it can't overflow.
 *
 *    Multiplicative
 *     May be able to increment without overflow.
 *     Don't need to extend the exponent to increment when normalising.
 *     Can use injection bits during the multiplication reduction tree,
 *      the problem with the carry up can be fixed afterwards with an
 *      increment (add for subnormal) or by spotting the carry up during
 *      the reduction.
 *
 *    FMA
 *     More like multiply.
 */


#include "symfpu/core/unpackedFloat.h"

#ifndef SYMFPU_ROUNDER
#define SYMFPU_ROUNDER

namespace symfpu {

template <class t>
  unpackedFloat<t> rounder (const typename t::fpt &format,
			    const typename t::rm &roundingMode,
			    const unpackedFloat<t> &uf) {

  typedef typename t::bwt bwt;
  typedef typename t::prop prop;
  typedef typename t::ubv ubv;
  typedef typename t::sbv sbv;

  //PRECONDITION(uf.valid(format));
  // Not a precondition because
  //  1. Exponent and significand may be extended.
  //  2. Their values may also be outside of the correct range.
  //
  // However some thing do hold:
  //  1. Leading bit of the significant is 1   (if you want to get a meaningful answer)
  //     (if not, a cancellation on the near path of add can cause
  //      this, but the result will not be used, so it can be incorrect)
  ubv psig(uf.getSignificand());
  bwt sigWidth(psig.getWidth());
  //PRECONDITION(psig.extract(sigWidth-1, sigWidth-1).isAllOnes());
  ubv sig(psig | unpackedFloat<t>::leadingOne(sigWidth));

  //  2. Must have round and sticky bits
  bwt targetSignificandWidth(unpackedFloat<t>::significandWidth(format));
  PRECONDITION(sigWidth >= targetSignificandWidth + 2);

  //  3. Must have at least enough exponent bits
  sbv exp(uf.getExponent());
  bwt expWidth(exp.getWidth());
  bwt targetExponentWidth(unpackedFloat<t>::exponentWidth(format));
  PRECONDITION(expWidth >= targetExponentWidth);

  // Also, do not round special values.
  // Note that this relies on these having default values and 
  // the code that calls the rounder constructing uf from parts.
  PRECONDITION(!uf.getNaN());
  PRECONDITION(!uf.getInf());
  PRECONDITION(!uf.getZero());



  // Optimisation : early underflow is correct in almost all cases
  //                only need to round if:
  //                   exponent >= minSubnormalExponent - 1


  /*** Normal or subnormal rounding? ***/
  prop normalRounding(exp >= unpackedFloat<t>::minNormalExponent(format).extend(expWidth - targetExponentWidth));


  /*** Round to correct significand. ***/
  ubv extractedSignificand(sig.extract(sigWidth - 1, sigWidth - targetSignificandWidth));

  bwt guardBitPosition(sigWidth - (targetSignificandWidth + 1));
  prop guardBit(sig.extract(guardBitPosition, guardBitPosition).isAllOnes());

  prop stickyBit(!sig.extract(guardBitPosition - 1,0).isAllZeros());
  

  // For subnormals, locating the guard and stick bits is a bit more involved
  sbv subnormalAmount(unpackedFloat<t>::maxSubnormalExponent(format).extend(expWidth - targetExponentWidth) - exp);
  prop belowLimit(subnormalAmount <= sbv::zero(expWidth));    // Not subnormal
  prop aboveLimit(subnormalAmount >= sbv(expWidth, targetSignificandWidth));  // Will underflow
  sbv subnormalShift(ITE((belowLimit || aboveLimit), sbv::zero(expWidth), subnormalAmount));

  ubv subnormalShiftPrepared(subnormalShift.toUnsigned().extend(sigWidth - expWidth));
  ubv guardLocation(ubv::one(targetSignificandWidth) << subnormalShiftPrepared);
  ubv stickyMask(guardLocation.decrement());


  prop subnormalGuardBit(!(extractedSignificand & guardLocation).isAllZeros());
  prop subnormalStickyBit(guardBit || stickyBit || 
			  !((extractedSignificand & stickyMask).isAllZeros()));




  // Can overflow but is handled
  ubv incrementedSignificand(extractedSignificand.modularIncrement());
  prop incrementedSignificandOverflow(incrementedSignificand.isAllZeros());

  ubv correctedIncrementedSignificand(ITE(!incrementedSignificandOverflow,
					  incrementedSignificand,
					  unpackedFloat<t>::leadingOne(unpackedFloat<t>::significandWidth(format))));


  ubv incrementAmount(guardLocation.modularLeftShift(1)); // Overflows (safely) in the case of rounding up to the least subnormal.
  ubv mask(guardLocation | stickyMask);
  ubv maskedSignificand(extractedSignificand & ~mask);

  ubv subnormalIncrementedSignificand(maskedSignificand.modularAdd(incrementAmount));
  prop subnormalIncrementedSignificandOverflow(subnormalIncrementedSignificand.isAllZeros());
  ubv subnomalCorrectedIncrementedSignificand(ITE(!subnormalIncrementedSignificandOverflow,
						  subnormalIncrementedSignificand,
						  unpackedFloat<t>::leadingOne(unpackedFloat<t>::significandWidth(format))));
 


  // Have to choose the right one dependent on rounding mode
  prop choosenGuardBit(ITE(normalRounding, guardBit, subnormalGuardBit));
  prop choosenStickyBit(ITE(normalRounding, stickyBit, subnormalStickyBit));
  
  prop significandEven(ITE(normalRounding,
			   extractedSignificand.extract(0,0).isAllZeros(),
			   ((extractedSignificand & incrementAmount).isAllZeros())));
  prop roundUpRNE(roundingMode == t::RNE() && choosenGuardBit && (choosenStickyBit || !significandEven));
  prop roundUpRNA(roundingMode == t::RNA() && choosenGuardBit);
  prop roundUpRTP(roundingMode == t::RTP() && !uf.getSign() && (choosenGuardBit || choosenStickyBit));
  prop roundUpRTN(roundingMode == t::RTN() &&  uf.getSign() && (choosenGuardBit || choosenStickyBit));
  prop roundUpRTZ(roundingMode == t::RTZ() && prop(false));
  prop roundUp(roundUpRNE || roundUpRNA || roundUpRTP || roundUpRTN || roundUpRTZ);

  ubv roundedSignificand(ITE(normalRounding,
			     ITE((!roundUp), extractedSignificand, correctedIncrementedSignificand),
			     ITE((!roundUp), maskedSignificand, subnomalCorrectedIncrementedSignificand)));



  /*** Round to correct exponent. ***/

  // The extend is almost certainly unnecessary (see specialised rounders)
  sbv extendedExponent(exp.extend(1));
  sbv incrementedExponent(extendedExponent.increment());

  prop incrementExponent(ITE(normalRounding,
			     incrementedSignificandOverflow,
			     subnormalIncrementedSignificandOverflow)
			 && roundUp);  // Rare...
  sbv correctedExponent(ITE(!incrementExponent,
			    extendedExponent,
			    incrementedExponent));

  // This can over and underflow but these values will not be used
  bwt currentExponentWidth(correctedExponent.getWidth());
  sbv roundedExponent(correctedExponent.contract(currentExponentWidth - targetExponentWidth));


  /*** Underflow and overflow ***/
  prop overflow(correctedExponent > unpackedFloat<t>::maxNormalExponent(format).extend(currentExponentWidth - targetExponentWidth));
  prop underflow(correctedExponent < unpackedFloat<t>::minSubnormalExponent(format).extend(currentExponentWidth - targetExponentWidth));

  // On overflow either return inf or max
  prop returnInf(roundingMode == t::RNE() || 
		 roundingMode == t::RNA() ||
		 (roundingMode == t::RTP() && !uf.getSign()) ||
		 (roundingMode == t::RTN() &&  uf.getSign()));   // Inf is more likely than max in most application scenarios

  // On underflow either return 0 or minimum subnormal
  prop returnZero(roundingMode == t::RNE() || 
		  roundingMode == t::RNA() ||
		  roundingMode == t::RTZ() ||
		  (roundingMode == t::RTP() &&  uf.getSign()) ||
		  (roundingMode == t::RTN() && !uf.getSign()));   // 0 is more likely than min in most application scenarios


  /*** Reconstruct ***/
  unpackedFloat<t> roundedResult(uf.getSign(), roundedExponent, roundedSignificand);

  unpackedFloat<t> inf(unpackedFloat<t>::makeInf(format, uf.getSign()));
  unpackedFloat<t> max(uf.getSign(), unpackedFloat<t>::maxNormalExponent(format), ubv::allOnes(targetSignificandWidth));
  unpackedFloat<t> min(uf.getSign(), unpackedFloat<t>::minSubnormalExponent(format), unpackedFloat<t>::leadingOne(targetSignificandWidth));
  unpackedFloat<t> zero(unpackedFloat<t>::makeZero(format, uf.getSign()));
  
  unpackedFloat<t> result(ITE(underflow,
			      ITE(returnZero, zero, min),
			      ITE(overflow,
				  ITE(returnInf, inf, max),
				  roundedResult)));

  POSTCONDITION(result.valid(format));

  return result;
 }

}

#endif
