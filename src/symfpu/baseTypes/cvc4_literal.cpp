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

#include "util/floatingpoint.h"   // cvc4_literal needs this but can't include it or it will create a loop
#include "symfpu/baseTypes/cvc4_literal.h"

namespace symfpu {
  namespace cvc4_literal {

    void iprecondition (const bool b) { Assert(b); }
    void ipostcondition (const bool b) { Assert(b); }
    void iinvariant (const bool b) { Assert(b); }


    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::one (const bitWidthType &w) { return bitVector<isSigned>(w,1); }

    template <bool isSigned>    
    bitVector<isSigned> bitVector<isSigned>::zero (const bitWidthType &w)  { return bitVector<isSigned>(w,0); }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::allOnes (const bitWidthType &w)  { return ~bitVector<isSigned>::zero(w); }
      
    template <bool isSigned>
    proposition bitVector<isSigned>::isAllOnes() const {return (*this == bitVector<isSigned>::allOnes(this->getWidth()));}
    template <bool isSigned>
    proposition bitVector<isSigned>::isAllZeros() const {return (*this == bitVector<isSigned>::zero(this->getWidth()));}


    /*** Operators ***/
    template <bool isSigned>    
    bitVector<isSigned> bitVector<isSigned>::operator << (unsigned s) const {
      IPRECONDITION(s <= this->getWidth());
      return this->CVC4BV::leftShift(CVC4BV(this->getWidth(),s));
    }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::operator << (const bitVector<isSigned> &op) const {
      return this->CVC4BV::leftShift(op);
    }


    template <>    
    bitVector<true> bitVector<true>::operator >> (uint64_t s) const {
      IPRECONDITION(s <= this->getWidth());
      
      return this->CVC4BV::arithRightShift(CVC4BV(this->getWidth(), (long unsigned int)s));
    }

    template <>
    bitVector<false> bitVector<false>::operator >> (uint64_t s) const {
      IPRECONDITION(s <= this->getWidth());
      
      return this->CVC4BV::logicalRightShift(CVC4BV(this->getWidth(), (long unsigned int)s));
    }



    template <>
    bitVector<true> bitVector<true>::operator >> (const bitVector<true> &op) const {
      return this->CVC4BV::arithRightShift(op);
    }

    template <>
    bitVector<false> bitVector<false>::operator >> (const bitVector<false> &op) const {
      return this->CVC4BV::logicalRightShift(op);
    }



    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::operator | (const bitVector<isSigned> &op) const { return this->CVC4BV::operator|(op); }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::operator & (const bitVector<isSigned> &op) const { return this->CVC4BV::operator&(op); }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::operator + (const bitVector<isSigned> &op) const { return this->CVC4BV::operator+(op); }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::operator - (const bitVector<isSigned> &op) const { return this->CVC4BV::operator-(op); }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::operator * (const bitVector<isSigned> &op) const { return this->CVC4BV::operator*(op); }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::operator - (void) const { return this->CVC4BV::operator-(); }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::operator ~ (void) const { return this->CVC4BV::operator~(); }
      
    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::increment () const {
      return *this + bitVector<isSigned>::one(this->getWidth());
    }
    
    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::decrement () const {
      return *this - bitVector<isSigned>::one(this->getWidth());
    }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::signExtendRightShift (const bitVector<isSigned> &op) const {
      return this->CVC4BV::arithRightShift(CVC4BV(this->getWidth(),op));
    }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::rightShiftStickyBit (const bitVector<isSigned> &op) const {
      bitVector<isSigned> stickyBit(ITE((op.orderEncode(this->getWidth()) & *this).isAllZeros(),
					bitVector<isSigned>::zero(this->getWidth()),
					bitVector<isSigned>::one(this->getWidth())));
      
      
      return this->CVC4BV::arithRightShift(CVC4BV(this->getWidth(),op)) | stickyBit;
    }


    /*** Modular opertaions ***/
    // No overflow checking so these are the same as other operations
    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::modularLeftShift (uint64_t s) const {
      IPRECONDITION(s <= this->getWidth());
      return *this << s;
    }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::modularIncrement () const {
      return this->increment();
    }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::modularAdd (const bitVector<isSigned> &op) const {
      return *this + op;
    }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::modularNegate () const {
      return -(*this);
    }


    
    
    /*** Comparisons ***/

    template <bool isSigned>    
    proposition bitVector<isSigned>::operator == (const bitVector<isSigned> &op) const { return this->CVC4BV::operator==(op); }


    template <>
    proposition bitVector<true>::operator <= (const bitVector<true> &op) const { 
      return this->signedLessThanEq(op);
    }

    template <>
    proposition bitVector<true>::operator >= (const bitVector<true> &op) const {
      return !(this->signedLessThan(op));
    }

    template <>
    proposition bitVector<true>::operator < (const bitVector<true> &op) const  {
      return this->signedLessThan(op);
    }

    template <>
    proposition bitVector<true>::operator > (const bitVector<true> &op) const  {
      return !(this->signedLessThanEq(op));
    }


    template <>
    proposition bitVector<false>::operator <= (const bitVector<false> &op) const { 
      return this->unsignedLessThanEq(op);
    }

    template <>
    proposition bitVector<false>::operator >= (const bitVector<false> &op) const {
      return !(this->unsignedLessThan(op));
    }

    template <>
    proposition bitVector<false>::operator < (const bitVector<false> &op) const  {
      return this->unsignedLessThan(op);
    }

    template <>
    proposition bitVector<false>::operator > (const bitVector<false> &op) const  {
      return !(this->unsignedLessThanEq(op));
    }



    /*** Type conversion ***/
    // CVC4 nodes make no distinction between signed and unsigned, thus ...
    template <bool isSigned>
    bitVector<true> bitVector<isSigned>::toSigned (void) const {
      return bitVector<true>(*this);
    }

    template <bool isSigned>
    bitVector<false> bitVector<isSigned>::toUnsigned (void) const {
      return bitVector<false>(*this);
    }



    /*** Bit hacks ***/

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::extend (bitWidthType extension) const {
      if (isSigned) {
	return this->CVC4BV::signExtend(extension);
      } else {
	return this->CVC4BV::zeroExtend(extension);
      }
    }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::contract (bitWidthType reduction) const {
      IPRECONDITION(this->getWidth() > reduction);

      return this->extract((this->getWidth() - 1) - reduction, 0);
    }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::resize (bitWidthType newSize) const {
      bitWidthType width = this->getWidth();

      if (newSize > width) {
	return this->extend(newSize - width);
      } else if (newSize < width) {
	return this->contract(width - newSize);
      } else {
	return *this;
      }
    }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::matchWidth (const bitVector<isSigned> &op) const {
      IPRECONDITION(this->getWidth() <= op.getWidth());
      return this->extend(op.getWidth() - this->getWidth());
    }


    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::append(const bitVector<isSigned> &op) const {
      return this->CVC4BV::concat(op);
    }

    // Inclusive of end points, thus if the same, extracts just one bit
    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::extract(bitWidthType upper, bitWidthType lower) const {
      IPRECONDITION(upper >= lower);
      return this->CVC4BV::extract(upper, lower);
    }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::orderEncode (bitWidthType w) const {
      bitVector<isSigned> tmp((bitVector<isSigned>::one(w + 1) << this->resize(w + 1)).decrement().contract(1));
      return tmp;
    }



    /*** Expanding operations ***/
    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::expandingAdd (const bitVector<isSigned> &op) const {
      bitVector<isSigned> x((*this).extend(1));
      bitVector<isSigned> y(     op.extend(1));

      return x + y;
    }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::expandingSubtract (const bitVector<isSigned> &op) const {
      bitVector<isSigned> x((*this).extend(1));
      bitVector<isSigned> y(     op.extend(1));

      return x - y;
    }

    template <bool isSigned>
    bitVector<isSigned> bitVector<isSigned>::expandingMultiply (const bitVector<isSigned> &op) const {
      bitVector<isSigned> x((*this).extend(this->getWidth()));
      bitVector<isSigned> y(     op.extend(this->getWidth()));

      return x * y;
    }


    // Explicit instantiation
    template class bitVector<true>;
    template class bitVector<false>;




    roundingMode traits::RNE (void) { return ::CVC4::roundNearestTiesToEven; };
    roundingMode traits::RNA (void) { return ::CVC4::roundNearestTiesToAway; };
    roundingMode traits::RTP (void) { return ::CVC4::roundTowardPositive; };
    roundingMode traits::RTN (void) { return ::CVC4::roundTowardNegative; };
    roundingMode traits::RTZ (void) { return ::CVC4::roundTowardZero; };


    // This is a literal back-end so props are actually bools
    // so these can be handled in the same way as the internal assertions above

    void traits::precondition(const prop &p) { Assert(p); return; }
    void traits::postcondition(const prop &p) { Assert(p); return; }
    void traits::invariant(const prop &p) { Assert(p); return; }

  };
};


