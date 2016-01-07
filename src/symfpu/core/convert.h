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
unpackedFloat<t> convert (const typename t::fpt &sourceFormat,
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

};

#endif
