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
** packing.h
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 03/06/14
**
** Algorithms for converting from a packed float (a bit vector) into
** the working, unpacked float format.  Should be instantiated with a
** traits structure from one of the baseTypes/ implementations.
**
*/

#include "symfpu/core/unpackedFloat.h"

#ifndef SYMFPU_PACKING
#define SYMFPU_PACKING

namespace symfpu {

  template<class t>
    unpackedFloat<t> unpack (const typename t::fpt format, const typename t::ubv &packedFloat) {
    typedef typename t::bwt bwt;
    typedef typename t::prop prop;
    typedef typename t::ubv ubv;
    typedef typename t::sbv sbv;

    bwt pWidth = format.packedWidth();
    bwt exWidth = format.packedExponentWidth();
    bwt sigWidth = format.packedSignificandWidth();

    PRECONDITION(packedFloat.getWidth() == pWidth);

    // Extract
    ubv packedSignificand(packedFloat.extract(sigWidth - 1, 0));
    ubv packedExponent(packedFloat.extract(sigWidth + exWidth - 1, sigWidth));
    prop sign(packedFloat.extract(pWidth - 1, sigWidth + exWidth).isAllOnes());

    // Analyse
    prop zeroExponent(packedExponent.isAllZeros());
    prop onesExponent(packedExponent.isAllOnes());
    prop zeroSignificand(packedSignificand.isAllZeros());

    // Identify the cases
    prop isZero(zeroExponent && zeroSignificand);
    prop isSubnormal(zeroExponent && !zeroSignificand);
    prop isNormal(!zeroExponent && !onesExponent);
    prop isInf(onesExponent && zeroSignificand);
    prop isNaN(onesExponent && !zeroSignificand);

    INVARIANT(isZero || isSubnormal || isNormal || isInf || isNaN);

    // Prepare the normal and subnormal cases
    bwt unpackedExWidth = unpackedFloat<t>::exponentWidth(format);
    bwt unpackedSigWidth = unpackedFloat<t>::significandWidth(format);

    INVARIANT(unpackedExWidth > exWidth); // To avoid overflow
    sbv biasedExponent(packedExponent.extend(unpackedExWidth - exWidth).toSigned() - unpackedFloat<t>::bias(format));

    ubv significandWithLeadingZero(packedSignificand.extend(unpackedSigWidth - sigWidth));
    ubv significandWithLeadingOne(unpackedFloat<t>::leadingOne(unpackedFloat<t>::significandWidth(format)) | significandWithLeadingZero);

    unpackedFloat<t> ufNormal(sign, biasedExponent, significandWithLeadingOne);
    unpackedFloat<t> ufSubnormalBase(sign, unpackedFloat<t>::minNormalExponent(format), significandWithLeadingZero);

    // Splice together
    unpackedFloat<t> uf(ITE(isNaN,
			    unpackedFloat<t>::makeNaN(format),
			    ITE(isInf,
				unpackedFloat<t>::makeInf(format, sign),
				ITE(isZero,
				    unpackedFloat<t>::makeZero(format, sign),
				    ITE(isNormal,
					ufNormal,
					ufSubnormalBase.normaliseUp(format) )))));

    POSTCONDITION(uf.valid(format));

    return uf;
  }


  template<class t>
    typename t::ubv pack (const typename t::fpt &format, const unpackedFloat<t> &uf) {
    typedef typename t::bwt bwt;
    typedef typename t::prop prop;
    typedef typename t::ubv ubv;
    typedef typename t::sbv sbv;

    PRECONDITION(uf.valid(format));

    // Sign
    ubv packedSign(ITE(uf.getSign(), ubv::one(1), ubv::zero(1)));

    // Exponent
    bwt packedExWidth = format.packedExponentWidth();
    ubv maxSig(ubv::allOnes(packedExWidth));
    ubv minSig(ubv::zero(packedExWidth));

    prop inNormalRange(uf.inNormalRange(format));
    prop inSubnormalRange(uf.inSubnormalRange(format));
    INVARIANT(inNormalRange || inSubnormalRange);        // Default values ensure this.

    sbv biasedSig(uf.getExponent() + unpackedFloat<t>::bias(format));
    // Will be correct for normal values only, subnormals may still be negative.
    ubv packedBiasedSig(biasedSig.toUnsigned().extract(packedExWidth - 1,0));


    // Significand
    bwt packedSigWidth = format.packedSignificandWidth();
    ubv unpackedSignificand(uf.getSignificand());

    INVARIANT(packedSigWidth == unpackedSignificand.getWidth() - 1);
    ubv dropLeadingOne(unpackedSignificand.extract(packedSigWidth - 1,0));
    ubv correctedSubnormal((unpackedSignificand >> (uf.getSubnormalAmount(format).toUnsigned())).extract(packedSigWidth - 1,0));

    
    // Encodings
    ubv packedNaN(maxSig.append(unpackedFloat<t>::nanPattern(format.packedSignificandWidth())));
    ubv packedInf(maxSig.append(dropLeadingOne));          // Uses the default value.
    ubv packedZero(minSig.append(dropLeadingOne));         // Uses the default value.
    ubv packedNormal(packedBiasedSig.append(dropLeadingOne));
    ubv packedSubnormal(minSig.append(correctedSubnormal));

    ubv result(packedSign.append(ITE(uf.getNaN(),
				     packedNaN,
				     ITE(uf.getInf(),
					 packedInf,
					 ITE(uf.getZero(),
					     packedZero,
					     ITE(inNormalRange,
						 packedNormal,
						 packedSubnormal))))));
    POSTCONDITION(result.getWidth() == format.packedWidth());

    return result;
  }

};

#endif
