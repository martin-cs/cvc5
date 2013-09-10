#include "cvc4_private.h"

#ifndef __CVC4__THEORY__FP__THEORY_FP_TYPE_RULES_H
#define __CVC4__THEORY__FP__THEORY_FP_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace fp {

class FloatingPointConstantTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {

    const FloatingPoint &f = n.getConst<FloatingPoint>();
    
    if (check) {
      if (!(f.t.exponent() > 1)) {
        throw TypeCheckingExceptionPrivate(n, "constant with invalid exponent size");
      }
      if (!(f.t.significand() > 1)) {
        throw TypeCheckingExceptionPrivate(n, "constant with invalid significand size");
      }
    }
    return nodeManager->mkFloatingPointType(f.t);
  }
};


class FpTypeRule {
public:

  /**
   * Compute the type for (and optionally typecheck) a term belonging
   * to the theory of fp.
   *
   * @param check if true, the node's type should be checked as well
   * as computed.
   */
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check)
    throw (TypeCheckingExceptionPrivate) {

    // TODO: implement me!
    Unimplemented();

  }

};/* class FpTypeRule */

}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__FP__THEORY_FP_TYPE_RULES_H */
