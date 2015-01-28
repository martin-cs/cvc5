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
** compare.h
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 25/08/14
**
** Comparison between floating-point numbers
**
*/

#include "symfpu/core/unpackedFloat.h"

#ifndef SYMFPU_COMPARE
#define SYMFPU_COMPARE

namespace symfpu {

  // SMT-LIB equality
  template <class t>
    typename t::prop smtlibEqual (const typename t::fpt &format, 
				  const unpackedFloat<t> &left,
				  const unpackedFloat<t> &right) {
    PRECONDITION(left.valid(format));
    PRECONDITION(right.valid(format));

    // Relies on a number of properties of the unpacked format
    // particularly the use of default exponents, significands and signs

    return (left.getNan() == right.getNan()) &&
      (left.getInf() == right.getInf()) &&
      (left.getZero() == right.getZero()) &&
      (left.getSign() == right.getSign()) &&
      (left.getExponent() == right.getExponent()) &&
      (left.getSignificand() == right.getSignificand());
  }
  
  // IEEE-754 Equality (not actually an equivalence relation but ...)
  template <class t>
    typename t::prop ieee754Equal (const typename t::fpt &format, 
				   const unpackedFloat<t> &left,
				   const unpackedFloat<t> &right) {

    typedef typename t::prop prop;

    PRECONDITION(left.valid(format));
    PRECONDITION(right.valid(format));

    prop neitherNan(!left.getNan() && !right.getNan());   // All comparison with NaN are false
    prop bothZero(left.getZero() && right.getZero());  // Both zeros are equal
    prop neitherZero(!left.getZero() && !right.getZero());


    return neitherNan &&
      (bothZero || (neitherZero &&
		    (left.getInf() == right.getInf() && 
		     left.getSign() == right.getSign() &&
		     left.getExponent() == right.getExponent() &&
		     left.getSignificand() == right.getSignificand())));
  }
  

  
  template <class t>
    typename t::prop lessThan (const typename t::fpt &format, 
			       const unpackedFloat<t> &left,
			       const unpackedFloat<t> &right) {

    typedef typename t::prop prop;

    PRECONDITION(left.valid(format));
    PRECONDITION(right.valid(format));

    // Optimisation : merge < and ==


    // All comparison with NaN are false
    prop neitherNan(!left.getNan() && !right.getNan());

    // Infinities are bigger than everything but themself
    prop eitherInf(left.getInf() || right.getInf());
    prop infCase(( left.isNegativeInf() && !right.isNegativeInf()) ||
		 (!left.isPositiveInf() &&  right.isPositiveInf()));


    // Both zero are equal
    prop eitherZero(left.getZero() || right.getZero());
    prop zeroCase(( left.getZero() && !right.getZero() && !right.getSign()) ||
		  (!left.getZero() &&   left.getSign() &&  right.getZero()));


    // Normal and subnormal

    prop negativeLessThanPositive(left.getSign() && !right.getSign());  // - < +
    prop positiveCase(!left.getSign() && !right.getSign() &&
		      ((left.getExponent() < right.getExponent()) ||
		       (left.getExponent() == right.getExponent() && 
			left.getSignificand() < right.getSignificand())));

    prop negativeCase(left.getSign() && right.getSign() &&
		      ((left.getExponent() > right.getExponent()) ||
		       (left.getExponent() == right.getExponent() && 
			left.getSignificand() > right.getSignificand())));
		 

    return neitherNan &&
      ITE(eitherInf,
	  infCase,
	  ITE(eitherZero,
	      zeroCase,
	      negativeLessThanPositive || positiveCase || negativeCase));
  }
  
  // Optimised combination of the two
  template <class t>
    typename t::prop lessThanOrEqual (const typename t::fpt &format, 
				      const unpackedFloat<t> &left,
				      const unpackedFloat<t> &right) {

    typedef typename t::prop prop;

    PRECONDITION(left.valid(format));
    PRECONDITION(right.valid(format));

    // Optimisation : merge < and ==


    // All comparison with NaN are false
    prop neitherNan(!left.getNan() && !right.getNan());

    // Infinities are bigger than everything but themself
    prop eitherInf(left.getInf() || right.getInf());
    prop infCase( (left.getInf() && right.getInf() && left.getSign() == right.getSign()) || 
		  left.isNegativeInf() ||
		  right.isPositiveInf());


    // Both zero are equal
    prop eitherZero(left.getZero() || right.getZero());
    prop zeroCase((left.getZero() && right.getZero()) ||
		  ( left.getZero() && !right.getSign()) ||
		  ( left.getSign() &&  right.getZero()));


    // Normal and subnormal

    prop negativeLessThanPositive(left.getSign() && !right.getSign());  // - < +
    prop positiveCase(!left.getSign() && !right.getSign() &&
		      ((left.getExponent() < right.getExponent()) ||
		       (left.getExponent() == right.getExponent() && 
			left.getSignificand() <= right.getSignificand())));

    prop negativeCase(left.getSign() && right.getSign() &&
		      ((left.getExponent() > right.getExponent()) ||
		       (left.getExponent() == right.getExponent() && 
			left.getSignificand() >= right.getSignificand())));
		 

    return neitherNan &&
      ITE(eitherInf,
	  infCase,
	  ITE(eitherZero,
	      zeroCase,
	      negativeLessThanPositive || positiveCase || negativeCase));
  }

}

#endif
