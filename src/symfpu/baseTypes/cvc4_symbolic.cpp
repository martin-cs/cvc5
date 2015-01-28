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
** cvc4_symbolic.cpp
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 05/01/15
**
** Non-templated functions for linking.
** It's best not to ask how this is built...
**
*/

#include "symfpu/baseTypes/cvc4_symbolic.h"

namespace symfpu {
  namespace cvc4_symbolic {

    roundingMode traits::RNE (void) { return roundingMode(0x01); };
    roundingMode traits::RNA (void) { return roundingMode(0x02); };
    roundingMode traits::RTP (void) { return roundingMode(0x04); };
    roundingMode traits::RTN (void) { return roundingMode(0x08); };
    roundingMode traits::RTZ (void) { return roundingMode(0x10); };


    template <>
    bitVector<true> bitVector<true>::maxValue (const bitWidthType &w) {
      bitVector<true> leadingZero(bitVector<true>::zero(1));
      bitVector<true> base(bitVector<true>::allOnes(w-1));
      
      return bitVector<true>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_CONCAT, leadingZero.node, base.node));
    }

    template <>
    bitVector<false> bitVector<false>::maxValue (const bitWidthType &w) {
      return bitVector<false>::allOnes(w);
    }

    template <>
    bitVector<true> bitVector<true>::minValue (const bitWidthType &w) {
      bitVector<true> leadingOne(bitVector<true>::one(1));
      bitVector<true> base(bitVector<true>::zero(w-1));
      
      return bitVector<true>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_CONCAT, leadingOne.node, base.node));
    }

    template <>
    bitVector<false> bitVector<false>::minValue (const bitWidthType &w) {
      return bitVector<false>::zero(w);
    }    
    
  };
};
