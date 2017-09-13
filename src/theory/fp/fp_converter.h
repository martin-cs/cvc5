/*********************                                                        */
/*! \file fp_convert.h
 ** \verbatim
 ** Original author: Martin Brain
 ** Major contributors:
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2014  University of Oxford
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Converts floating-point nodes to bit-vector expressions. ]]
 **
 ** [[ Uses the symfpu library to convert from floating-point operations
 **    to bit-vectors and propositions allowing the theory to be solved by
 **    'bit-blasting'. ]]
 **/

#include "theory/valuation.h"

#include "context/cdhashmap.h"
#include "context/cdlist.h"

#include "util/floatingpoint.h"

#include "symfpu/core/unpackedFloat.h"
#include "symfpu/baseTypes/cvc4_symbolic.h"

#ifndef __CVC4__THEORY__FP__FP_CONVERTER_H
#define __CVC4__THEORY__FP__FP_CONVERTER_H


namespace CVC4 {
namespace theory {
namespace fp {

  struct PairTypeNodeHashFunction {
    size_t operator()(const std::pair<TypeNode, TypeNode> &p) const;
  };

  // To simplify the naming of various types
  namespace symfpuSymbolic {
    typedef ::symfpu::cvc4_symbolic::traits traits;   // Use the CVC4 symbolic back-end
    typedef ::symfpu::unpackedFloat<traits> uf;
    typedef traits::rm rm;
    typedef traits::fpt fpt;
    typedef traits::prop prop;
    typedef traits::ubv ubv;
    typedef traits::sbv sbv;
  };

  class fpConverter {
  protected :
    typedef symfpuSymbolic::traits traits;
    typedef symfpuSymbolic::uf uf;
    typedef symfpuSymbolic::rm rm;
    typedef symfpuSymbolic::fpt fpt;
    typedef symfpuSymbolic::prop prop;
    typedef symfpuSymbolic::ubv ubv;
    typedef symfpuSymbolic::sbv sbv;

    typedef context::CDHashMap<Node, uf, NodeHashFunction> fpMap;
    typedef context::CDHashMap<Node, rm, NodeHashFunction> rmMap;
    typedef context::CDHashMap<Node, prop, NodeHashFunction> boolMap;
    typedef context::CDHashMap<Node, ubv, NodeHashFunction> ubvMap;
    typedef context::CDHashMap<Node, sbv, NodeHashFunction> sbvMap;

    fpMap f;
    rmMap r;
    boolMap b;
    ubvMap u;
    sbvMap s;


    /* These functions take a symfpu object and convert it to a node.
     * These should ensure that constant folding it will give a
     * constant of the right type.
     */

    Node ufToNode (const fpt &,const uf &) const;
    Node rmToNode (const rm &) const;
    Node propToNode (const prop &) const;
    Node ubvToNode (const ubv &) const;
    Node sbvToNode (const sbv &) const;



    /* Store the uninterpretted functions used to create
     * non-deterministic components of non-deterministic floats. */

    typedef context::CDHashMap<TypeNode, Node, TypeNodeHashFunction> uninterprettedFunctionMap;

    Node roundingModeUF;
    uninterprettedFunctionMap NaNMap;
    uninterprettedFunctionMap infMap;
    uninterprettedFunctionMap zeroMap;
    uninterprettedFunctionMap signMap;
    uninterprettedFunctionMap exponentMap;
    uninterprettedFunctionMap significandMap;

    Node buildRoundingModeUFApp (Node);
    Node buildNaNUFApp (Node);
    Node buildInfUFApp (Node);
    Node buildZeroUFApp (Node);
    Node buildSignUFApp (Node);
    Node buildExponentUFApp (Node);
    Node buildSignificandUFApp (Node);

    uf buildComponents(TNode current);


  public :
    context::CDList<Node> additionalAssertions;

    fpConverter (context::UserContext*);

    /** Adds a node to the conversion, returns the converted node */
    Node convert (TNode);

    /** Gives the node representing the value of a given variable */
    Node getValue (Valuation &, TNode);

  };


}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__FP__THEORY_FP_H */
