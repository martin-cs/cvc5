/*
** Copyright (C) 2016 Martin Brain
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
** convert.h
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 03/02/14
**
** Conversion from unpacked floats in one format to another.
**
*/

#include "symfpu/core/unpackedFloat.h"
#include "symfpu/core/rounder.h"

#ifndef SYMFPU_CONVERT
#define SYMFPU_CONVERT

namespace symfpu {

template <class t>
unpackedFloat<t> convertFloatToFloat (const typename t::fpt &sourceFormat,
				      const typename t::fpt &targetFormat,
				      const typename t::rm &roundingMode,
				      const unpackedFloat<t> &input) {

  PRECONDITION(input.valid(sourceFormat));

  typedef typename t::bwt bwt;
  //typedef typename t::prop prop;
  //typedef typename t::ubv ubv;
  //typedef typename t::sbv sbv;

  // increased includes equality
  bool exponentIncreased = unpackedFloat<t>::exponentWidth(sourceFormat) <= unpackedFloat<t>::exponentWidth(targetFormat);
  bool significandIncreased = unpackedFloat<t>::significandWidth(sourceFormat) <= unpackedFloat<t>::significandWidth(targetFormat);

  bwt expExtension = (exponentIncreased) ? unpackedFloat<t>::exponentWidth(targetFormat) - unpackedFloat<t>::exponentWidth(sourceFormat) : 0;
  bwt sigExtension = (significandIncreased) ? unpackedFloat<t>::significandWidth(targetFormat) - unpackedFloat<t>::significandWidth(sourceFormat) : 0;

  unpackedFloat<t> extended(input.extend(expExtension, sigExtension));

  // Format sizes are literal so it is safe to branch on them
  if (exponentIncreased && significandIncreased) {
    // Fast path strict promotions

    POSTCONDITION(extended.valid(targetFormat));
    
    return extended;

  } else {

    unpackedFloat<t> rounded(rounder(targetFormat, roundingMode, extended));

    unpackedFloat<t> result(ITE(input.getNaN(),
				unpackedFloat<t>::makeNaN(targetFormat),
				ITE(input.getInf(),
				    unpackedFloat<t>::makeInf(targetFormat, input.getSign()),
				    ITE(input.getZero(),
					unpackedFloat<t>::makeZero(targetFormat, input.getSign()),
					rounded))));
    
    POSTCONDITION(result.valid(targetFormat));
    
    return result;
  }
}


template <class t>
  unpackedFloat<t> convertUBVToFloat (const typename t::fpt &targetFormat,
				      const typename t::rm &roundingMode,
				      const typename t::ubv &input) {

  typedef typename t::bwt bwt;
  typedef typename t::prop prop;
  typedef typename t::sbv sbv;
  typedef typename t::fpt fpt;

  bwt inputWidth(input.getWidth());
  
  // Devise an appropriate format 
  bwt initialExponentWidth(bitsToRepresent<bwt>(inputWidth) + 1); // +1 as unsigned -> signed
  fpt initialFormat(initialExponentWidth, inputWidth);

  // Build
  unpackedFloat<t> initial(prop(false), sbv(initialExponentWidth, inputWidth), input);
  
  // Normalise
  unpackedFloat<t> normalised(initial.normaliseUpDetectZero(initialFormat));

  // Round (the conversion will catch the cases where no rounding is needed)
  return convertFloatToFloat(initialFormat, targetFormat, roundingMode, normalised);
 }

 
template <class t>
  unpackedFloat<t> convertSBVToFloat (const typename t::fpt &targetFormat,
				      const typename t::rm &roundingMode,
				      const typename t::sbv &input) {

  typedef typename t::bwt bwt;
  typedef typename t::prop prop;
  typedef typename t::sbv sbv;
  typedef typename t::fpt fpt;

  bwt inputWidth(input.getWidth());
  
  // Devise an appropriate format 
  bwt initialExponentWidth(bitsToRepresent<bwt>(inputWidth) + 1); // +1 as unsigned -> signed
  fpt initialFormat(initialExponentWidth, inputWidth + 1);        // +1 as signed -> unsigned

  // Work out the sign
  prop negative(input < sbv::zero(inputWidth));

  // Build
  unpackedFloat<t> initial(negative, sbv(initialExponentWidth, inputWidth), (abs<t,sbv>(input.extend(1))).toUnsigned());
  
  // Normalise
  unpackedFloat<t> normalised(initial.normaliseUpDetectZero(initialFormat));

  // Round (the conversion will catch the cases where no rounding is needed)
  return convertFloatToFloat(initialFormat, targetFormat, roundingMode, normalised);
 }


 template <class t>
   unpackedFloat<t> convertFloatToUBV (const typename t::fpt &format,
				       const typename t::rm &roundingMode,
				       const unpackedFloat<t> &uf,
				       const typename t::bwt &targetWidth) {
   
   typedef typename t::bwt bwt;
   typedef typename t::prop prop;
   typedef typename t::ubv ubv;
   typedef typename t::sbv sbv;

   
   // Invalid cases
   prop specialValue(uf.getInf() || uf.getNaN());

   sbv exponent(uf.getExponent());
   bwt exponentWidth(exponent.getWidth());

   sbv largestExponent(exponentWidth, targetWidth);
   prop tooLarge(uf.getExponent() >=  largestExponent);

   prop undefinedResult(specialValue || uf.getZero() || tooLarge || uf.getSign());
   probabilityAnnotation<t>(undefinedResult, LIKELY); // Convertable values are rare


   // Align
   ubv expandedSignificand(uf.getSignificand().extend(targetWidth + 1)); // Start with the significand in the sticky position.
   sbv shiftAmount(collar<t>(exponent.modularIncrement().modularIncrement(),  // Overflow lost in the "too large" case
			     sbv::zero(exponentWidth),
			     largestExponent)); // Equal to bit width, thus shift right across
   ubv convertedShiftAmount(shiftAmount.contract(bitsToRepresent(largestExponent) + 1 /* +1 for sign, safe due to collar */
						 ).toUnsigned().matchWidth(expandedSignificand()));
   ubv aligned(expandedSignificand << convertedShiftAmount); // Safe by collar


   // Fixed position round
   significandRounderResult<t> rounded(fixedPositionRound(roundingMode, prop(false),
							  aligned, targetWidth,
							  prop(false), prop(false)));
   // Note that incrementExponent is ignored as it only happens when the rounding overflows
   // Sign is also "optimised" as it is only used in the case of positive
   
   ubv result(ITE(undefinedResult,
		  ubv::zero(targetWidth),
		  rounded.significand));

   return result;
 }
   
}

#endif
