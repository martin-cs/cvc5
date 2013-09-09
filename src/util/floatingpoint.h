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
  class CVC4_PUBLIC FloatingPointSize {
    /*
      Class invariants:
      * e > 1
      * s > 1
     */

  private :
    unsigned e;
    unsigned s;

  public :
    FloatingPointSize (unsigned _e, unsigned _s) : e(_e), s(_s)
    {
      assert(e > 1);
      assert(s > 1);
    }

    inline unsigned exponent (void) const {
      return this->e;
    }

    inline unsigned significand (void) const {
      return this->s;
    }

    bool operator ==(const FloatingPointSize& fps) const {
      return (e == fps.e) && (s == fps.s);
    }

  }; /* class FloatingPointSize */



#define ROLL(X,N) (((X) << (N)) | ((X) >> (8*sizeof((X)) - (N)) ))

  struct CVC4_PUBLIC FloatingPointSizeHashFunction {
    inline size_t operator() (const FloatingPointSize& fpt) const {
      return size_t(ROLL(fpt.exponent(), 4*sizeof(unsigned)) |
		    fpt.significand());
    }
  }; /* struct FloatingPointSizeHashFunction */










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
    FloatingPointSize t;
    /* \todo Floating point literal in correct form */
  public :
    FloatingPoint () : t(0,0) {
      assert(0);
    }

    bool operator ==(const FloatingPoint& f) const {
      if (!(t == f.t)) return false; 
      assert(0);
      return false;
    }
  }; /* class FloatingPoint */


  struct CVC4_PUBLIC FloatingPointHashFunction {
    inline size_t operator() (const FloatingPoint& rm) const {
      assert(0);
      return size_t(1);
    }
  }; /* struct FloatingPointHashFunction */







  /**
   * The parameter type for the conversions to floating point.
   */
  class CVC4_PUBLIC FloatingPointConvertSort {
  public :
    FloatingPointSize t;

    FloatingPointConvertSort (unsigned _e, unsigned _s)
      : t(_e,_s) {}

    bool operator ==(const FloatingPointConvertSort& fpcs) const {
      return t == fpcs.t;
    }
 
  };

  struct CVC4_PUBLIC FloatingPointConvertSortHashFunction {
    inline size_t operator() (const FloatingPointConvertSort& fpcs) const {
      FloatingPointSizeHashFunction f;
      return f(fpcs.t) ^ 0x43005300;
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
      UnsignedHashFunction< ::CVC4::BitVectorSize > f;
      return 	0x46504256 ^ f(fptbv.bvs);
    }
  }; /* struct FloatingPointToBVHashFunction */




  inline std::ostream& operator <<(std::ostream& os, const FloatingPoint& fp) CVC4_PUBLIC;
  inline std::ostream& operator <<(std::ostream& os, const FloatingPoint& fp) {
    assert(0);
  return os << "<floating point number goes here>";
}

  inline std::ostream& operator <<(std::ostream& os, const FloatingPointSize& fps) CVC4_PUBLIC;
  inline std::ostream& operator <<(std::ostream& os, const FloatingPointSize& fps) {
    assert(0);
    return os << "(_ FloatingPoint " << fps.exponent() << " " << fps.significand() << ")";
  }

  inline std::ostream& operator <<(std::ostream& os, const FloatingPointConvertSort& fpcs) CVC4_PUBLIC;
  inline std::ostream& operator <<(std::ostream& os, const FloatingPointConvertSort& fpcs) {
    assert(0);
    return os << "((_ to_fp " << fpcs.t.exponent() << " " << fpcs.t.significand() << ")";
  }




}/* CVC4 namespace */

#endif /* __CVC4__FLOATINGPOINT_H */
