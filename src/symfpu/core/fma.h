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
** fma.h
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 20/05/15
**
** Fused multiply and add :
**  fma(R,A,B,C) = round(R, A * B + C)
**
*/

#include "symfpu/core/unpackedFloat.h"
#include "symfpu/core/ite.h"
#include "symfpu/core/rounder.h"
#include "symfpu/core/multiply.h"
#include "symfpu/core/convert.h"
#include "symfpu/core/add.h"


#ifndef SYMFPU_FMA
#define SYMFPU_FMA

namespace symfpu {


 template <class t>
   unpackedFloat<t> fma (const typename t::fpt &format,
			 const typename t::rm &roundingMode,
			 const unpackedFloat<t> &leftMultiply,
			 const unpackedFloat<t> &rightMultiply,
			 const unpackedFloat<t> &addArgument) {
   
   typedef typename t::bwt bwt;
   typedef typename t::prop prop;
   typedef typename t::ubv ubv;
   typedef typename t::sbv sbv;
   typedef typename t::fpt fpt;
  
   PRECONDITION(leftMultiply.valid(format));
   PRECONDITION(rightMultiply.valid(format));
   PRECONDITION(addArgument.valid(format));

   unpackedFloat<t> multiplyResult(arithmeticMultiply(format, leftMultiply, rightMultiply));
   
   fpt extendedFormat(format.exponentWidth() + 1, format.significandWidth() * 2);
   INVARIANT(multiplyResult.valid(extendedFormat));

   // Rounding mode doesn't matter as this is a strict extension
   unpackedFloat<t> extendedAddArgument(convert(format, extendedFormat, t::RTZ(), addArgument));

   unpackedFloat<t> additionResult(arithmeticAdd(extendedFormat, roundingMode, multiplyResult, extendedAddArgument, prop(true)));

   unpackedFloat<t> roundedResult(rounder(format, roundingMode, additionResult));

   // multiplyResult is in extended format
   // It is not zero, inf or NaN so it only matters when addArgument is zero when it would be returned
   unpackedFloat<t> result(addAdditionSpecialCases(format,
						   roundingMode,
						   multiplyResult, // TODO : Format is wrong
						   addArgument,
						   addMultiplySpecialCases(format,
									   leftMultiply,
									   rightMultiply,
									   roundedResult),
						   prop(true)));
   
   POSTCONDITION(result.valid(format));
   
   return result;
 }


};

#endif
