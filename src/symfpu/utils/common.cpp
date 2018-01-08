/*
** Copyright (C) 2018 Martin Brain
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
** common.cpp
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 05/08/14
**
** Commonly used utility functions.
**
*/

#include "symfpu/utils/common.h"


namespace symfpu {
  uint64_t previousPowerOfTwo (uint64_t x) {
    assert(x > 1);
    //PRECONDITION(x > 1);

    uint64_t current = 1;
    uint64_t next = current << 1;
    
    while (next < x) {
      current = next;
      next <<= 1;
    }

    return current;
  }

  
  uint64_t leftmostBit (uint64_t x) {
    assert(x > 1);
    //PRECONDITION(x > 1);

    uint64_t current = 1;
    uint64_t next = current << 1;
    
    while (next <= x) {
      current = next;
      next <<= 1;
    }

    return current;
  }
}
