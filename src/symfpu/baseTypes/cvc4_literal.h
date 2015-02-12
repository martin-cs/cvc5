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
** cvc4_literal.h
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 12/06/14
**
** A back-end for symfpu that uses CVC4 datatypes to perform arbitrary
** precision floating-point computations.  Used to implement the CVC4
** literal floating-point type.
**
*/

// Symfpu headers
#include "symfpu/utils/properties.h"
#include "symfpu/core/ite.h"

// CVC4 headers

/* Despite using some structures from this header, it is not included
 * as the intended use is that this will be included in it! */
//#include "util/floatingpoint.h"
#include "util/bitvector.h"


/** Can't use cvc4_assert as this is part of util/floatingpoint.h and
  * so is public. The following is a temporary hack!
  * \todo FIX! */
#include <assert.h>
#define UNFINISHED(X) assert(0)

#ifndef SYMFPU_CVC4_LITERAL
#define SYMFPU_CVC4_LITERAL


namespace symfpu {
  namespace cvc4_literal {

    // Internal versions -- for use in this namespace only
    void iprecondition (const bool b);
    void ipostcondition (const bool b);
    void iinvariant (const bool b);


    typedef unsigned bitWidthType;
    typedef bool proposition;
    typedef ::CVC4::RoundingMode roundingMode;


    // Type function
    template <bool T> struct signedToLiteralType;

    template <> struct signedToLiteralType< true> {
      typedef int literalType;
    };
    template <> struct signedToLiteralType<false> {
      typedef  unsigned int literalType;
    };



    template <bool isSigned>
    class bitVector : public ::CVC4::BitVector {
    protected :
      typedef typename signedToLiteralType<isSigned>::literalType literalType;
      typedef ::CVC4::BitVector CVC4BV;

      friend bitVector<!isSigned>;    // To allow conversion between the types
      friend ite<proposition, bitVector<isSigned> >;   // For ITE


    public :
      bitVector (const bitWidthType w, const unsigned v) : CVC4BV(w,v) {}
      bitVector (const bitVector<isSigned> &old) : CVC4BV(old) {}
      bitVector (const CVC4BV &old) : CVC4BV(old) {}


      bitWidthType getWidth (void) const {
	return getSize();
      }


      /*** Constant creation and test ***/
      
      static bitVector<isSigned> one (const bitWidthType &w) { return bitVector<isSigned>(w,1); }
      static bitVector<isSigned> zero (const bitWidthType &w)  { return bitVector<isSigned>(w,0); }
      static bitVector<isSigned> allOnes (const bitWidthType &w)  { return ~bitVector<isSigned>::zero(w); }
      
      inline proposition isAllOnes() const {return (*this == bitVector<isSigned>::allOnes(this->getWidth()));}
      inline proposition isAllZeros() const {return (*this == bitVector<isSigned>::zero(this->getWidth()));}


      /*** Operators ***/
      inline bitVector<isSigned> operator << (unsigned s) const {
	IPRECONDITION(s <= this->getWidth());
	return this->CVC4BV::leftShift(CVC4BV(this->getWidth(),s));
      }

      inline bitVector<isSigned> operator << (const bitVector<isSigned> &op) const {
	return this->CVC4BV::leftShift(op);
      }

      inline bitVector<isSigned> operator >> (uint64_t s) const {
	IPRECONDITION(s <= this->getWidth());

	if (isSigned) {
	  return this->CVC4BV::arithRightShift(CVC4BV(this->getWidth(), (long unsigned int)s));
	} else {
	  return this->CVC4BV::logicalRightShift(CVC4BV(this->getWidth(), (long unsigned int)s));
	}
      }

      inline bitVector<isSigned> operator >> (const bitVector<isSigned> &op) const {
	if (isSigned) {
	  return this->CVC4BV::arithRightShift(op);
	} else {
	  return this->CVC4BV::logicalRightShift(op);
	}
      }


      /* Inherited but ...
       * *sigh* if we use the inherited version then it will return a
       * CVC4::BitVector which can be converted back to a
       * bitVector<isSigned> but isn't done automatically when working
       * out types for templates instantiation.  ITE is a particular
       * problem as expressions and constants no longer derive the
       * same type.  There aren't any good solutions in C++, we could
       * use CRTP but Liana wouldn't appreciate that, so the following
       * pointless wrapping functions are needed.
       */

      inline bitVector<isSigned> operator | (const bitVector<isSigned> &op) const { return this->CVC4BV::operator|(op); }
      inline bitVector<isSigned> operator & (const bitVector<isSigned> &op) const { return this->CVC4BV::operator&(op); }
      inline bitVector<isSigned> operator + (const bitVector<isSigned> &op) const { return this->CVC4BV::operator+(op); }
      inline bitVector<isSigned> operator - (const bitVector<isSigned> &op) const { return this->CVC4BV::operator-(op); }
      inline bitVector<isSigned> operator * (const bitVector<isSigned> &op) const { return this->CVC4BV::operator*(op); }
      inline bitVector<isSigned> operator - (void) const { return this->CVC4BV::operator-(); }
      inline bitVector<isSigned> operator ~ (void) const { return this->CVC4BV::operator~(); }
      

      inline bitVector<isSigned> increment () const {
	return *this + bitVector<isSigned>::one(this->getWidth());
      }

      inline bitVector<isSigned> decrement () const {
	return *this - bitVector<isSigned>::one(this->getWidth());
      }

      inline bitVector<isSigned> signExtendRightShift (const bitVector<isSigned> &op) const {
	return this->CVC4BV::arithRightShift(CVC4BV(this->getWidth(),op));
      }

      bitVector<isSigned> rightShiftStickyBit (const bitVector<isSigned> &op) const {
	UNFINISHED("rightShiftStickyBit");
	return this->CVC4BV::arithRightShift(CVC4BV(this->getWidth(),op));
      }


      /*** Modular opertaions ***/
      // No overflow checking so these are the same as other operations
      inline bitVector<isSigned> modularLeftShift (uint64_t s) const {
	IPRECONDITION(s <= this->getWidth());
	return *this << s;
      }

      inline bitVector<isSigned> modularIncrement () const {
	return this->increment();
      }

      inline bitVector<isSigned> modularAdd (const bitVector<isSigned> &op) const {
	return *this + op;
      }

      inline bitVector<isSigned> modularNegate () const {
	return -(*this);
      }




      /*** Comparisons ***/

      /* Inherited ... ish ... */
      inline proposition operator == (const bitVector<isSigned> &op) const { return this->CVC4BV::operator==(op); }
      inline proposition operator <= (const bitVector<isSigned> &op) const { return this->CVC4BV::operator<=(op); }
      inline proposition operator >= (const bitVector<isSigned> &op) const { return this->CVC4BV::operator>=(op); }
      inline proposition operator < (const bitVector<isSigned> &op) const  { return this->CVC4BV::operator< (op); }
      inline proposition operator > (const bitVector<isSigned> &op) const  { return this->CVC4BV::operator> (op); }


      /*** Type conversion ***/
      // CVC4 nodes make no distinction between signed and unsigned, thus ...
      bitVector<true> toSigned (void) const {
	return bitVector<true>(*this);
      }
      bitVector<false> toUnsigned (void) const {
	return bitVector<false>(*this);
      }



      /*** Bit hacks ***/

      inline bitVector<isSigned> extend (bitWidthType extension) const {
	if (isSigned) {
	  return this->CVC4BV::signExtend(extension);
	} else {
	  return this->CVC4BV::zeroExtend(extension);
	}
      }

      inline bitVector<isSigned> contract (bitWidthType reduction) const {
	IPRECONDITION(this->getWidth() > reduction);

	return this->extract(this->getWidth() - reduction, 0);
      }

      inline bitVector<isSigned> resize (bitWidthType newSize) const {
	bitWidthType width = this->getWidth();

	if (newSize > width) {
	  return this->extend(newSize - width);
	} else if (newSize < width) {
	  return this->contract(width - newSize);
	} else {
	  return *this;
	}
      }

      bitVector<isSigned> append(const bitVector<isSigned> &op) const {
	return this->CVC4BV::concat(op);
      }

      // Inclusive of end points, thus if the same, extracts just one bit
      bitVector<isSigned> extract(bitWidthType upper, bitWidthType lower) const {
	IPRECONDITION(upper >= lower);
	return this->CVC4BV::extract(upper, lower);
      }

      bitVector<isSigned> orderEncode (bitWidthType w) const {
	UNFINISHED("orderEncode");
      }



      /*** Expanding operations ***/

      inline bitVector<isSigned> expandingAdd (const bitVector<isSigned> &op) const {
	bitVector<isSigned> x((*this).extend(1));
	bitVector<isSigned> y(     op.extend(1));

	return x + y;
      }

      inline bitVector<isSigned> expandingSubtract (const bitVector<isSigned> &op) const {
	bitVector<isSigned> x((*this).extend(1));
	bitVector<isSigned> y(     op.extend(1));

	return x - y;
      }

      inline bitVector<isSigned> expandingMultiply (const bitVector<isSigned> &op) const {
	bitVector<isSigned> x((*this).extend(this->getWidth()));
	bitVector<isSigned> y(     op.extend(this->getWidth()));

	return x * y;
      }



    };



    class floatingPointTypeInfo : public ::CVC4::FloatingPointSize {
    protected :
      typedef ::CVC4::FloatingPointSize CVC4FPS;

      friend ite<proposition, floatingPointTypeInfo>;   // For ITE

    public :
      floatingPointTypeInfo(unsigned exp, unsigned sig) : CVC4FPS(exp, sig) {}
      floatingPointTypeInfo(const floatingPointTypeInfo &old) : CVC4FPS(old) {}
      floatingPointTypeInfo(const CVC4FPS &old) : CVC4FPS(old) {}
      
      bitWidthType exponentWidth(void) const    { return this->exponent(); }
      bitWidthType significandWidth(void) const { return this->significand(); }
      
      bitWidthType packedWidth(void) const            { return this->exponentWidth() + this->significandWidth(); }
      bitWidthType packedExponentWidth(void) const    { return this->exponentWidth(); }
      bitWidthType packedSignificandWidth(void) const { return this->significandWidth() - 1; }
      
    };


    // Wrap up the types into one template parameter
    class traits {
    public :
      typedef bitWidthType bwt;
      typedef roundingMode rm;
      typedef floatingPointTypeInfo fpt;
      typedef proposition prop;
      typedef bitVector< true> sbv;
      typedef bitVector<false> ubv;

      static roundingMode RNE (void);
      static roundingMode RNA (void);
      static roundingMode RTP (void);
      static roundingMode RTN (void);
      static roundingMode RTZ (void);

      static void precondition(const prop &p);
      static void postcondition(const prop &p);
      static void invariant(const prop &p);
    };




  };

#define CVC4LITITEDFN(T) template <>					\
    struct ite<cvc4_literal::proposition, T> {				\
    static const T & iteOp (const cvc4_literal::proposition &cond,	\
			    const T &l,					\
			    const T &r) {				\
      if (cond) {							\
	return l;							\
      } else {								\
	return r;							\
      }									\
    }									\
  }

  CVC4LITITEDFN(cvc4_literal::traits::rm);
  CVC4LITITEDFN(cvc4_literal::traits::prop);
  CVC4LITITEDFN(cvc4_literal::traits::sbv);
  CVC4LITITEDFN(cvc4_literal::traits::ubv);

};

#endif



