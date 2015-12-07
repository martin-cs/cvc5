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
** operations.h
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 15/11/14
**
** A number of compound operations on bit-vectors.  These are default
** implementations to reduce the amount of code that is needed for a
** back-end (and the risk of making a mistake).  Back-ends can provide
** their own implementations of these if they can handle them in a
** smarter way than the default.
**
*/

#include <cassert>

#ifndef SYMFPU_OPERATIONS
#define SYMFPU_OPERATIONS

namespace symfpu {

  /*** Expanding operations ***/
  template <class t, class bv>
  inline bv expandingAdd (const bv &op1, const bv &op2) {
    PRECONDITION(op1.getWidth() == op2.getWidth());

    bv x(op1.extend(1));
    bv y(op2.extend(1));
    
    return x + y;
  }

  template <class t, class bv>
  inline bv expandingSubtract (const bv &op1, const bv &op2) {
    PRECONDITION(op1.getWidth() == op2.getWidth());

    bv x(op1.extend(1));
    bv y(op2.extend(1));
    
    return x - y;
  }

  template <class t, class bv>
  inline bv expandingMultiply (const bv &op1, const bv &op2) {
    typename t::bwt width = op1.getWidth();
    PRECONDITION(width == op2.getWidth());
    
    bv x(op1.extend(width));
    bv y(op2.extend(width));

    return x * y;
  }


  /*** Conditional Operations ***/
  template <class t, class bv, class prop>
  inline bv conditionalIncrement (const prop &p, const bv &b) {
    PRECONDITION(!p || b <  bv::maxValue(b.getWidth()));
    
    bv incremented(b.modularIncrement());
    return bv(ITE(p, incremented, b));
  }

  template <class t, class bv, class prop>
  inline bv conditionalLeftShiftOne (const prop &p, const bv &b) {
    PRECONDITION(!p || (b.extract(b.getWidth() - 1, b.getWidth() - 1).isAllZeros()));

    bv shifted(b.modularLeftShift(1ULL));
    return bv(ITE(p, shifted, b));
  }


  /*** Probability Annotations ***/
  enum probability {
    VERYLIKELY = 100,
    LIKELY = 50,
    NEUTRAL = 0,
    UNLIKELY = -50,
    VERYUNLIKELY = -100
  };

  template <class t, class prop>
  inline void probabilityAnnotation (const prop &, const probability &) {
    // Back-ends can make use of this information if they want
    return;
  }


  /*** Max and min ***/
  template <class t, class bv>
  inline bv max (const bv &op1, const bv &op2) {
    return ITE(op1 <= op2, op2, op1);
  }

  template <class t, class bv>
  inline bv min (const bv &op1, const bv &op2) {
    return ITE(op1 <= op2, op1, op2);
  }


  // TODO : count leading zeros
}

#endif
