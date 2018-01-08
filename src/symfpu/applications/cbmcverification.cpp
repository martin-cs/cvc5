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
** cbmcverification.cpp
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 03/06/14
**
** A set of functions each with one or more properties to verify.
** These make use of the simpleExecutable implementation of bit-vectors
** to convert the operations into `executable' ones that CBMC can reason
** about. 
**
*/

#include <assert.h>

#if 0
#if 0
// Doesn't work -- need to work at call level
static int assumeFirstPrecondition = 1;

//#define PRECONDITION(X) if (assumeFirstPrecondition) { __CPROVER_assume(X); assumeFirstPrecondition = 0; } else { assert(X); }
#else
#define PRECONDITION(X) assert(X)
#endif

#define POSTCONDITION(X) assert(X)
#define INVARIANT(X) assert(X)
#endif


#include "symfpu/baseTypes/simpleExecutable.h"
#include "symfpu/applications/implementations.h"
#include "symfpu/applications/executable.h"



/*** We are using the simple executable back-end to give 
     an executable semantics to the symfpu code. ***/

typedef symfpu::simpleExecutable::traits traits;
typedef traits::fpt fpt;
typedef traits::rm rm;
typedef symfpu::unpackedFloat<traits> uf;



/*** To avoid unnecessary repetition and redundancy, individual tests are given as macros ***/
#define UNARYFUNCTIONTEST(BV, NAME)   void NAME##Harness (BV bv) {	\
    BV computed = test::NAME(precision, bv);				\
    BV reference = test::NAME##Reference(precision, bv);		\
    bool compare = test::smtlibEqualReference(precision, computed, reference); \
    assert(compare);							\
    return;								\
  }

#define UNARYPREDICATETEST(BV, NAME)   void NAME##Harness (BV bv) { \
    bool computed = test::NAME(precision, bv);			    \
    bool reference = test::NAME##Reference(precision, bv);	    \
    bool compare = (computed == reference);			    \
    assert(compare);						    \
    return;							    \
  } 

#define BINARYPREDICATETEST(BV, NAME)   void NAME##Harness (BV bv1, BV bv2) { \
    bool computed = test::NAME(precision, bv1, bv2);			\
    bool reference = test::NAME##Reference(precision, bv1, bv2);	\
    bool compare = (computed == reference);				\
    assert(compare);							\
    return;								\
  }

#define BINARYFUNCTIONTEST(BV, RM, NAME)   void NAME##RM##Harness (BV bv1, BV bv2) { \
    BV computed = test::NAME(precision, traits::RM(), bv1, bv2);	\
    BV reference = test::NAME##Reference(precision, traits::RM(), bv1, bv2); \
    bool compare = test::smtlibEqualReference(precision, computed, reference); \
    assert(compare);							\
    return;								\
  }





/*** Compare symfpu with CBMC's in-built model of float ***/

namespace singlePrecision {
  
  fpt precision(8,24);
  
  typedef executableTests<uint32_t, float, traits> test;
  
  UNARYFUNCTIONTEST(uint32_t, unpackPack)
  UNARYFUNCTIONTEST(uint32_t, negate)
  UNARYFUNCTIONTEST(uint32_t, absolute)

  UNARYPREDICATETEST(uint32_t, isNormal)
  UNARYPREDICATETEST(uint32_t, isSubnormal)
  UNARYPREDICATETEST(uint32_t, isZero)
  UNARYPREDICATETEST(uint32_t, isInfinite)
  UNARYPREDICATETEST(uint32_t, isPositive)
  UNARYPREDICATETEST(uint32_t, isNegative)

  BINARYPREDICATETEST(uint32_t, smtlibEqual)
  BINARYPREDICATETEST(uint32_t, ieee754Equal)
  BINARYPREDICATETEST(uint32_t, lessThan)
  BINARYPREDICATETEST(uint32_t, lessThanOrEqual)

  BINARYFUNCTIONTEST(uint32_t, RNE, add)
  BINARYFUNCTIONTEST(uint32_t, RNA, add)
  BINARYFUNCTIONTEST(uint32_t, RTP, add)
  BINARYFUNCTIONTEST(uint32_t, RTN, add)
  BINARYFUNCTIONTEST(uint32_t, RTZ, add)

  BINARYFUNCTIONTEST(uint32_t, RNE, multiply)
  BINARYFUNCTIONTEST(uint32_t, RNA, multiply)
  BINARYFUNCTIONTEST(uint32_t, RTP, multiply)
  BINARYFUNCTIONTEST(uint32_t, RTN, multiply)
  BINARYFUNCTIONTEST(uint32_t, RTZ, multiply)

  BINARYFUNCTIONTEST(uint32_t, RNE, sub)
  BINARYFUNCTIONTEST(uint32_t, RNA, sub)
  BINARYFUNCTIONTEST(uint32_t, RTP, sub)
  BINARYFUNCTIONTEST(uint32_t, RTN, sub)
  BINARYFUNCTIONTEST(uint32_t, RTZ, sub)

}



/*** Compare symfpu with CBMC's in-built model of double ***/

namespace doublePrecision {
  
  fpt precision(11,53);
  
  typedef executableTests<uint64_t, double, traits> test;
  
  UNARYFUNCTIONTEST(uint64_t, unpackPack)
  UNARYFUNCTIONTEST(uint64_t, negate)
  UNARYFUNCTIONTEST(uint64_t, absolute)

  UNARYPREDICATETEST(uint64_t, isNormal)
  UNARYPREDICATETEST(uint64_t, isSubnormal)
  UNARYPREDICATETEST(uint64_t, isZero)
  UNARYPREDICATETEST(uint64_t, isInfinite)
  UNARYPREDICATETEST(uint64_t, isPositive)
  UNARYPREDICATETEST(uint64_t, isNegative)

  BINARYPREDICATETEST(uint64_t, smtlibEqual)
  BINARYPREDICATETEST(uint64_t, ieee754Equal)
  BINARYPREDICATETEST(uint64_t, lessThan)
  BINARYPREDICATETEST(uint64_t, lessThanOrEqual)

  BINARYFUNCTIONTEST(uint64_t, RNE, add)
  BINARYFUNCTIONTEST(uint64_t, RNA, add)
  BINARYFUNCTIONTEST(uint64_t, RTP, add)
  BINARYFUNCTIONTEST(uint64_t, RTN, add)
  BINARYFUNCTIONTEST(uint64_t, RTZ, add)

  BINARYFUNCTIONTEST(uint64_t, RNE, multiply)
  BINARYFUNCTIONTEST(uint64_t, RNA, multiply)
  BINARYFUNCTIONTEST(uint64_t, RTP, multiply)
  BINARYFUNCTIONTEST(uint64_t, RTN, multiply)
  BINARYFUNCTIONTEST(uint64_t, RTZ, multiply)

  BINARYFUNCTIONTEST(uint64_t, RNE, sub)
  BINARYFUNCTIONTEST(uint64_t, RNA, sub)
  BINARYFUNCTIONTEST(uint64_t, RTP, sub)
  BINARYFUNCTIONTEST(uint64_t, RTN, sub)
  BINARYFUNCTIONTEST(uint64_t, RTZ, sub)

}




/*** Token main to ease the use of goto-cc ***/

int main (void) {
  return 0;
}
