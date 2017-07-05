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
    PRECONDITION(IMPLIES(p, b <  bv::maxValue(b.getWidth())));
    
    bv incremented(b.modularIncrement());
    return bv(ITE(p, incremented, b));
  }

  template <class t, class bv, class prop>
  inline bv conditionalDecrement (const prop &p, const bv &b) {
    PRECONDITION(IMPLIES(p, bv::minValue(b.getWidth()) < b));
    
    bv incremented(b.modularDecrement());
    return bv(ITE(p, incremented, b));
  }

  template <class t, class bv, class prop>
  inline bv conditionalLeftShiftOne (const prop &p, const bv &b) {
    typename t::bwt w(b.getWidth());
    PRECONDITION(IMPLIES(p, (b.extract(w - 1, w - 1).isAllZeros())));

    bv shifted(b.modularLeftShift(bv::one(w)));
    return bv(ITE(p, shifted, b));
  }

  template <class t, class bv, class prop>
  inline bv conditionalRightShiftOne (const prop &p, const bv &b) {
    typename t::bwt w(b.getWidth());
    // PRECONDITION(IMPLIES(p, (b.extract(0, 0).isAllZeros())));  // Adder uses and compensates for this case.

    bv shifted(b.modularRightShift(bv::one(w)));
    return bv(ITE(p, shifted, b));
  }

  template <class t, class bv, class prop>
  inline bv conditionalNegate (const prop &p, const bv &b) {
    typename t::bwt w(b.getWidth());
    PRECONDITION(w >= 2);
    PRECONDITION(IMPLIES(p, !(b.extract(w - 1, w - 1).isAllOnes() &&
			      b.extract(w - 2,     0).isAllZeros())));
    
    return bv(ITE(p, -b, b));
  }

  template <class t, class bv>
  inline bv abs(const bv &b) {
    return conditionalNegate<t, bv, typename t::prop>(b < bv::zero(b.getWidth()), b);
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

  template <class t, class bv>
  inline bv collar(const bv &op, const bv &lower, const bv &upper) {
    return ITE(op < lower,
	       lower,
	       ITE(upper < op,
		   upper,
		   op));
  }
  

  /*** Unary/Binary operations ***/
  template <class t, class bv, class prop, class bwt>
  inline bv countLeadingZerosRec (const bv &op, const bwt position, const prop &allPreceedingZeros) {
    typename t::bwt w(op.getWidth());
    
    PRECONDITION(0 <= position && position < w);
    
    bv bit(op.extract(position, position));
    
    prop isLeadingOne(allPreceedingZeros && (bit.isAllOnes()));
    prop continuingZero(allPreceedingZeros && (bit.isAllZeros()));

    if (position == 0) {
      return ITE(isLeadingOne, bv(w, w - 1), bv(w, w));
    } else {
      return ITE(isLeadingOne,
		 bv(w, w - (position + 1)),
		 countLeadingZerosRec<t>(op, position - 1, continuingZero));
    }
  }
  
  template <class t, class bv>
  inline bv countLeadingZeros (const bv &op) {
    typedef typename t::bwt bwt;
    typedef typename t::prop prop;    
    bwt w(op.getWidth());

    return countLeadingZerosRec<t>(op, w - 1, prop(true));
  }
  
  // This is sort of the opposite of count trailing 1's (a.k.a. clz(reverse(not(x))) )
  template <class t, class bv>
  inline bv orderEncode (const bv &op) {
    typename t::bwt w(op.getWidth());
    
    //PRECONDITION(bv::zero(w) <= op && op <= bv(w, w)); // Not needed as using modular shift

    bv tmp((bv::one(w + 1).modularLeftShift(op.resize(w + 1))).modularDecrement().extract(w-1,0));
    return tmp;
  }


  /*** Custom shifts ***/
  // 1 if and only if the right shift moves at least one 1 out of the word
  template <class t, class bv>
  inline bv rightShiftStickyBit (const bv &op, const bv &shift) {
    bv stickyBit(ITE((orderEncode<t>(shift) & op).isAllZeros(),
		     bv::zero(op.getWidth()),
		     bv::one(op.getWidth())));
    
    return stickyBit;
  }


  /*** Dividers ***/
  template <class t>
  struct resultWithRemainderBit {
    typedef typename t::ubv ubv;
    typedef typename t::prop prop;
    
    ubv result;
    prop remainderBit;
    
  resultWithRemainderBit(const ubv &o, const prop &r) : result(o), remainderBit(r) {}
  resultWithRemainderBit(const resultWithRemainderBit<t> &old) : result(old.result), remainderBit(old.remainderBit) {}
  };
  
  // x and y are fixed-point numbers in the range [1,2)
  // Compute o \in [0.5,2), r \in [0,\delta) such that:  x = o*y + r
  // Return (o, r != 0)
  template <class t>
  inline resultWithRemainderBit<t> fixedPointDivide (const typename t::ubv &x, const typename t::ubv &y) {
    typename t::bwt w(x.getWidth());

    // Same width and both have MSB ones
    PRECONDITION(y.getWidth() == w);
    PRECONDITION(x.extract(w - 1, w - 1).isAllOnes());
    PRECONDITION(y.extract(w - 1, w - 1).isAllOnes());

    typedef typename t::ubv ubv;
    
    // Not the best way of doing this but pretty universal
    ubv ex(x.append(ubv::zero(w - 1)));
    ubv ey(y.extend(w - 1));

    ubv div(ex / ey);
    ubv rem(ex % ey);

    return resultWithRemainderBit<t>(div.extract(w - 1, 0), !(rem.isAllZeros()));
  }

  
  // x is a fixed-point number in the range [1,4) with 2/p bits
  // Compute o \in [1,sqrt(2)), r \in [0,o*2 + 1) such that x = o*o + r with 1/p bits
  // Return (o, r != 0)
  template <class t>
  inline resultWithRemainderBit<t> fixedPointSqrt (const typename t::ubv &x) {
    typedef typename t::bwt bwt;
    typedef typename t::ubv ubv;
    typedef typename t::prop prop;

    // The default algorithm given here isn't a great one
    // However it is simple and has a very simple termination criteria.
    // Plus most symbolic back ends will prefer
    // o = nondet(), r = nondet(), assert(r < o*2 + 1), assert(x = o*o + r)

    bwt inputWidth(x.getWidth());
    bwt outputWidth(inputWidth - 1);

    // To compare against, we need to pad x to 2/2p
    ubv xcomp(x.append(ubv::zero(inputWidth - 2))); 

    // Start at 1
    ubv working(ubv::one(outputWidth) << ubv(outputWidth, outputWidth - 1));

    bwt location;
    for (location = outputWidth - 1; location > 0; --location) { // Offset by 1 for easy termination
      ubv shift(ubv(outputWidth, location - 1));
      
      ubv candidate(working | (ubv::one(outputWidth) << shift));

      prop addBit(expandingMultiply<t, ubv>(candidate, candidate) <= xcomp);

      working = working | (ubv(addBit).extend(outputWidth - 1) << shift);
    }
    
    return resultWithRemainderBit<t>(working, !(expandingMultiply<t, ubv>(working, working) == xcomp));
  }
  
}

#endif
