/*********************                                                        */
/*! \file floatingpoint.h
 ** \verbatim
 ** Original author: Martin Brain
 ** Major contributors: 
 ** Minor contributors (to current version): 
 ** This file is *NOT* part of the CVC4 project.
 ** Copyright (c) 2013  University of Oxford
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Utility functions for working with floating point theories. ]]
 **
 ** [[ This file contains the data structures used by the constant and
 **    parametric types of the floating point theory. ]]
 **/

#include <assert.h>

#include "cvc4_public.h"


#ifndef __CVC4__FLOATINGPOINT_H
#define __CVC4__FLOATINGPOINT_H

#include "util/bitvector.h"

namespace CVC4 {



  /**
   * A type to represent the rounding mode sort
   */
  struct RoundingModeType {};



  /**
   * Floating point sorts are parameterised by two non-zero constants
   * giving the width (in bits) of the exponent and significand
   * (including the hidden bit).
   */
  class CVC4_PUBLIC FloatingPointType {
    /*
      Class invariants:
      * e > 0
      * s > 0
     */

  private :
    unsigned e;
    unsigned s;

  public :
    FloatingPointType (unsigned _e, unsigned _s) : e(_e), s(_s)
    {
      assert(e > 0);
      assert(s > 0);
    }

    inline unsigned exponent (void) const {
      return this->e;
    }

    inline unsigned significand (void) const {
      return this->s;
    }
  }; /* class FloatingPointType */



#define ROLL(X,N) (((X) << (N)) | ((X) >> (8*sizeof((X)) - (N)) ))

  struct CVC4_PUBLIC FloatingPointTypeHashFunction {
    inline size_t operator() (const FloatingPointType& fpt) const {
      return size_t(ROLL(fpt.exponent()), 4*sizeof(unsigned) |
		    fpt.significand());
    }
  }; /* struct FloatingPointTypeHashFunction */










  /**
   * A concrete instance of the rounding mode sort
   */
  enum CVC4_PUBLIC RoundingMode {
    roundNearestTiesToEven,
    roundNearestTiesToAway,
    roundTowardPositive,
    roundTowardNegative,
    roundTowardZero
  }; /* enum RoundingMode */

  struct CVC4_PUBLIC RoundingModeHashFunction {
    inline size_t operator() (const RoundingMode& rm) const {
      return size_t(rm);
    }
  }; /* struct RoundingModeHashFunction */










  /**
   * A concrete floating point number
   */

  class CVC4_PUBLIC FloatingPoint {
  protected :
    FloatingPointType t;
    /* \todo Floating point literal in correct form */
  public :
    FloatingPoint () {
      assert(0);
    }
  }; /* class FloatingPoint */


  struct CVC4_PUBLIC FloatingPointHashFunction {
    inline size_t operator() (const FloatingPoint& rm) const {
      return size_t(rm);
    }
  }; /* struct FloatingPointHashFunction */






  /**
   * The parameter type for the conversions to floating point.
   */
  class CVC4_PUBLIC FloatingPointConvertSort {
  public :
    FloatingPointType type;

    FloatingPointConvertSort (unsigned _e, unsigned _s)
      : type(e,s) {}
  };

  struct CVC4_PUBLIC FloatingPointConvertSortHashFunction {
    inline size_t operator() (const FloatingPointConvertSort& fpcs) const {
      return FloatingPointTypeHashFunction(fpcs->type) ^ 0x43005300;
    }
  }; /* struct FloatingPointConvertSortHashFunction */








  /**
   * The parameter type for the conversion to bit vector.
   */
  class CVC4_PUBLIC FloatingPointToBV {
  public :
    BitVectorSize bvs;

    FloatingPointToBV (unsigned s)
      : bvs(s) {}
    operator unsigned () const { return bvs; }
  };

  struct CVC4_PUBLIC FloatingPointToBVHashFunction {
    inline size_t operator() (const FloatingPointToBV& fptbv) const {
      return 	0x46504256 ^
	UnsignedHashFunction< ::CVC4::BitVectorSize >(fp;
    }
  }; /* struct FloatingPointToBVHashFunction */




}/* CVC4 namespace */

#endif /* __CVC4__FLOATINGPOINT_H */
