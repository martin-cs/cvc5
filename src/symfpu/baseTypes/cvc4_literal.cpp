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
** cvc4_literal.cpp
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 26/01/15
**
** Non-templated functions for linking.
** It's best not to ask how this is built...
**
*/

#include "symfpu/baseTypes/cvc4_literal.h"

namespace symfpu {
  namespace cvc4_literal {

    void iprecondition (const bool b) { Assert(b); }
    void ipostcondition (const bool b) { Assert(b); }
    void iinvariant (const bool b) { Assert(b); }

    roundingMode traits::RNE (void) { return ::CVC4::roundNearestTiesToEven; };
    roundingMode traits::RNA (void) { return ::CVC4::roundNearestTiesToAway; };
    roundingMode traits::RTP (void) { return ::CVC4::roundTowardPositive; };
    roundingMode traits::RTN (void) { return ::CVC4::roundTowardNegative; };
    roundingMode traits::RTZ (void) { return ::CVC4::roundTowardZero; };

  };
};
