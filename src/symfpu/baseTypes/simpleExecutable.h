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
** simpleExecutable.h
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 03/06/14
**
** The most simple executable implementation of bit-vectors.
** Limited in the ranges it supports but fast and suitable for reasoning.
**
** Unless otherwise stated, bit operations require all operands to have the
** same widths and the result will have the same width (SMT-LIB style,
** but see the 'expanding' instructions below).  Also underflow and
** overflow are considered errors (unlike SMT-LIB but see the 'modular' instructions
** below) although error checking is not perfect as overflows in the
** underlying data type can mask errors.
**
*/

#include "symfpu/utils/properties.h"
#include "symfpu/core/ite.h"

#include <assert.h>
#include <stdint.h>
#include <limits.h>

#ifndef SYMFPU_SIMPLE_EXECUTABLE
#define SYMFPU_SIMPLE_EXECUTABLE

namespace symfpu {
  namespace simpleExecutable {
    
    // Internal versions -- for use in this namespace only
    void iprecondition (const bool b);
    void ipostcondition (const bool b);
    void iinvariant (const bool b);


    // Must be larger than the number of bit used in the bit-vector type to avoid overflow
    typedef uint8_t bitWidthType;


    // Separate from bit-vectors so that C++ typing is more helpful
    class proposition {
    private :
      bool value;

    public :
      proposition(bool v) : value(v) {}
      proposition(const proposition &old) : value(old.value) {} 

      proposition operator! (void) const {
	return proposition(!this->value);
      }

      proposition operator&& (const proposition &op) const {
	return proposition(this->value && op.value);
      }

      proposition operator|| (const proposition &op) const {
	return proposition(this->value || op.value);
      }

      proposition operator == (const proposition &op) const {
	return proposition(this->value == op.value);
      }

      proposition operator ^ (const proposition &op) const {
	return proposition(this->value ^ op.value);
      }

      // Not appropriate in all instantiations
      bool toBool () const {
	return this->value;
      }

      //IPRECONDITION(trueCase.width() == falseCase.width());

    };


    
    class roundingMode {
    private :
      int value;
      
    public :
      roundingMode (int v) : value(v) {}
      roundingMode (const roundingMode &old) : value(old.value) {}
      
      roundingMode & operator = (const roundingMode &op) {
	this->value = op.value;
	return (*this);
      }
      
      proposition operator == (const roundingMode &op) const {
	return proposition(this->value == op.value);
      }

      // Only for executable
      int getValue (void) const {
	return this->value;
      }
    };
    






    template <typename T> struct modifySignedness;

    template <> struct modifySignedness< int64_t> { 
      typedef uint64_t unsignedVersion; 
      typedef  int64_t   signedVersion; 
    };
    template <> struct modifySignedness<uint64_t> { 
      typedef uint64_t unsignedVersion; 
      typedef  int64_t   signedVersion; 
    };



    template <class T>
    class bitVector {
    protected :
      bitWidthType width;
      T value;

      static bitWidthType maxWidth (void) {
	return sizeof(T)*CHAR_BIT;
      }

      static T nOnes (bitWidthType n) {
	if (n == 0) {
	  return 0;
	} else {
	  // Not (1 << n) - 1 to avoid overflow for n = maxWidth()
	  bitWidthType shift = bitVector<T>::maxWidth() - n;
	  return ((~0ULL) << shift) >> shift;
	}
      }

      // Bit vectors should store values in 2's complement using the full width
      // (and thus may have significant bits outside the width).
      // Thus need to make sure the value stored is representable within
      // bit-vectors of the specified width.
      static bool isRepresentable (const bitWidthType w, const T v);

      // Modular operations need to reduce operations back to
      // something representable.
      static T makeRepresentable (const bitWidthType w, const T v);
      

    public :

      // Ideally should protect but is used in subnormal rounding
      bitVector (const bitWidthType w, const T v) : width(w), value(v)
      {
	IPRECONDITION(width <= bitVector<T>::maxWidth()); 
	IPRECONDITION(0 < width); 
	IPRECONDITION(bitVector<T>::isRepresentable(w,v));
      }

      bitVector (const bitVector<T> &old) : width(old.width), value(old.value) {}
      
      // Constructors
      //   non-det   on other instances but not this so that
      //             instantiation catches this




      bitWidthType getWidth (void) const {
	return this->width;
      }
      
      // Would it be better to not have this and only have copy?
      bitVector<T> & operator= (const bitVector<T> &op) {
	IPRECONDITION(op.width == this->width);
	
	this->value = op.value;
	
	return (*this);
      }


      /*** Constant creation and test ***/

      static bitVector<T> one (const bitWidthType &w) { return bitVector<T>(w,1); }
      static bitVector<T> zero (const bitWidthType &w)  { return bitVector<T>(w,0); }
      static bitVector<T> allOnes (const bitWidthType &w)  { return bitVector<T>(w,bitVector<T>::nOnes(w)); }
      
      inline proposition isAllOnes() const {return proposition(((~this->value) & nOnes(this->width)) == 0);}
      inline proposition isAllZeros() const {return proposition(this->value == 0);}

      

      /*** Operators ***/
      // Need to inline the operations where possible
      inline bitVector<T> operator << (uint64_t s) const {
	IPRECONDITION(s <= this->width);
	return bitVector<T>(this->width, this->value << s);
      }

      inline bitVector<T> operator << (const bitVector<T> &op) const {
	IPRECONDITION(op.value >= 0 && op.value < this->width);
	return bitVector<T>(this->width, this->value << op.value);
      }

      inline bitVector<T> operator >> (uint64_t s) const {
	IPRECONDITION(s <= this->width);
	return bitVector<T>(this->width, this->value >> s);
      }

      inline bitVector<T> operator >> (const bitVector<T> &op) const {
	IPRECONDITION(op.value >= 0 && op.value < this->width);
	return bitVector<T>(this->width, this->value >> op.value);
      }

      inline bitVector<T> operator | (const bitVector<T> &op) const {
	IPRECONDITION(this->width == op.width);
	return bitVector<T>(this->width, this->value | op.value);
      }

      inline bitVector<T> operator & (const bitVector<T> &op) const {
	IPRECONDITION(this->width == op.width);
	return bitVector<T>(this->width, this->value & op.value);
      }

      inline bitVector<T> operator + (const bitVector<T> &op) const {
	IPRECONDITION(this->width == op.width);
	return bitVector<T>(this->width, this->value + op.value);
      }

      inline bitVector<T> operator - (const bitVector<T> &op) const {
	IPRECONDITION(this->width == op.width);
	return bitVector<T>(this->width, this->value - op.value);
      }

      bitVector<T> operator - (void) const;
      bitVector<T> operator ~ (void) const;

      inline bitVector<T> increment () const {
	return bitVector<T>(this->width, this->value + 1);
      }

      inline bitVector<T> decrement () const {
	return bitVector<T>(this->width, this->value - 1);
      }

      bitVector<T> signExtendRightShift (const bitVector<T> &op) const;
      bitVector<T> rightShiftStickyBit (const bitVector<T> &op) const;


      /*** Modular opertaions ***/
      bitVector<T> modularLeftShift (uint64_t s) const;

      inline bitVector<T> modularIncrement () const {
	return bitVector<T>(this->width, 
			    bitVector<T>::makeRepresentable(this->width, this->value + 1));
      }

      inline bitVector<T> modularAdd (const bitVector<T> &op) const {
	return bitVector<T>(this->width, 
			    bitVector<T>::makeRepresentable(this->width, 
							    this->value + op.value));
      }

      bitVector<T> modularNegate () const;



      /*** Expanding operations ***/

      inline bitVector<T> expandingAdd (const bitVector<T> &op) const {
	IPRECONDITION(this->width == op.width);
	return bitVector<T>(this->width + 1, this->value + op.value);
      }

      inline bitVector<T> expandingSubtract (const bitVector<T> &op) const {
	IPRECONDITION(this->width == op.width);
	return bitVector<T>(this->width + 1, this->value - op.value);
      }

      inline bitVector<T> expandingMultiply (const bitVector<T> &op) const {
	IPRECONDITION(this->width == op.width);
	return bitVector<T>(this->width * 2, this->value * op.value);
      }



      /*** Comparisons ***/

      inline proposition operator == (const bitVector<T> &op) const {
	IPRECONDITION(this->width == op.width);
	return proposition(this->value == op.value);
      }

      inline proposition operator <= (const bitVector<T> &op) const {
	IPRECONDITION(this->width == op.width);
	return proposition(this->value <= op.value);
      }

      inline proposition operator >= (const bitVector<T> &op) const {
	IPRECONDITION(this->width == op.width);
	return proposition(this->value >= op.value);
      }

      inline proposition operator < (const bitVector<T> &op) const {
	IPRECONDITION(this->width == op.width);
	return proposition(this->value < op.value);
      }

      inline proposition operator > (const bitVector<T> &op) const {
	IPRECONDITION(this->width == op.width);
	return proposition(this->value > op.value);
      }


      /*** Type conversion ***/

      bitVector<typename modifySignedness<T>::signedVersion> toSigned (void) const;
      bitVector<typename modifySignedness<T>::unsignedVersion> toUnsigned (void) const;



      /*** Bit hacks ***/

      inline bitVector<T> extend (bitWidthType extension) const {
	IPRECONDITION(this->width + extension <= bitVector<T>::maxWidth());

	// No extension needed, even in the signed case as already correctly represented
	return bitVector<T>(this->width + extension, this->value);
      }

      inline bitVector<T> contract (bitWidthType reduction) const {
	IPRECONDITION(this->width > reduction);

	return bitVector<T>(this->width - reduction, this->value);
      }

      inline bitVector<T> resize (bitWidthType newSize) const {
	return bitVector<T>(newSize, 
			    bitVector<T>::makeRepresentable(newSize, this->value));
      }



      bitVector<T> append(const bitVector<T> &op) const;

      // Inclusive of end points, thus if the same, extracts just one bit
      bitVector<T> extract(bitWidthType upper, bitWidthType lower) const;

      bitVector<T> orderEncode (bitWidthType w) const;

      // Only meaningful for executable implementations
      T contents (void) const { return this->value; }

    };

    
    
    // In SMT-LIB style -- significand includes hidden bit
    class floatingPointTypeInfo {
    private :
      bitWidthType exponentBits;
      bitWidthType significandBits;
      
    public :
      floatingPointTypeInfo (bitWidthType eb, bitWidthType sb) : exponentBits(eb), significandBits(sb) {
	IPRECONDITION(eb > 1);
	IPRECONDITION(sb > 1);
      }
      
      floatingPointTypeInfo (const floatingPointTypeInfo &old) : 
      exponentBits(old.exponentBits), significandBits(old.significandBits) {}
      
      floatingPointTypeInfo & operator= (const floatingPointTypeInfo &old) {
	this->exponentBits = old.exponentBits;
	this->significandBits = old.significandBits;
	
	return *this;
      }

      bitWidthType exponentWidth(void) const    { return this->exponentBits; }
      bitWidthType significandWidth(void) const { return this->significandBits; }

      
      bitWidthType packedWidth(void) const            { return this->exponentBits + this->significandBits; }
      bitWidthType packedExponentWidth(void) const    { return this->exponentBits; }
      bitWidthType packedSignificandWidth(void) const {	return this->significandBits - 1; }

      
    };



    
    // Wrap up the types into one template parameter
    class traits {
    public :
      typedef bitWidthType bwt;
      typedef roundingMode rm;
      typedef floatingPointTypeInfo fpt;
      typedef proposition prop;
      typedef bitVector< int64_t> sbv;
      typedef bitVector<uint64_t> ubv;

      static roundingMode RNE(void);
      static roundingMode RNA(void);
      static roundingMode RTP(void);
      static roundingMode RTN(void);
      static roundingMode RTZ(void);

      static void precondition(const prop &p) { iprecondition(p.toBool()); return; }
      static void postcondition(const prop &p) { ipostcondition(p.toBool()); return; }
      static void invariant(const prop &p) { iinvariant(p.toBool()); return; }
    };

  }; 


#define SEITEDFN(T) template <>						\
    struct ite<simpleExecutable::proposition, T> {			\
    static const T & iteOp (const simpleExecutable::proposition &cond,	\
			    const T &l,					\
			    const T &r) {				\
      if (cond.toBool()) {						\
	return l;							\
      } else {								\
	return r;							\
      }									\
    }									\
  }

  SEITEDFN(simpleExecutable::traits::rm);
  SEITEDFN(simpleExecutable::traits::prop);
  SEITEDFN(simpleExecutable::traits::sbv);
  SEITEDFN(simpleExecutable::traits::ubv);

  // Ideally check (trueCase.width() == falseCase.width()))

};



#endif
