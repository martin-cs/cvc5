/*********************                                                        */
/*! \file generated_ecodings.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Automatically generated encodings and other optimal encodings.
 **
 ** Implementation of bitblasting functions for various operators.
 **/

#ifndef __CVC4__GENERATED__ENCODINGS_H
#define __CVC4__GENERATED__ENCODINGS_H

#include "cvc4_private.h"
#include "expr/node.h"
#include "theory/bv/bitblast_utils.h"
#include "theory/bv/theory_bv_utils.h"
#include "prop/cnf_stream.h"
#include "theory/bv/options.h"

#include <ostream>
#include <cmath>

namespace CVC4 {

namespace theory {
namespace bv {

template<class T>
std::pair<T, std::pair<T, T> > inline optimalMaxGadget(const T a,
                                                           const T b,
                                                           const T a_max,
                                                           const T b_max,
                                                           CVC4::prop::CnfStream* cnf) {
  Unreachable();
}

template<class T>
std::pair<T, std::pair<T, T> > inline optimalSMaxGadget(const T a,
                                                        const T b,
                                                        CVC4::prop::CnfStream* cnf) {
  Unreachable();
}


template<class T>
void inline optimalSMax(const std::vector<T>& a,
                       const std::vector<T>& b,
                       std::vector<T>& bits,
                       CVC4::prop::CnfStream* cnf) {
  Unreachable();
}

template<class T>
std::pair<T, std::pair<T, T> > inline optimalMinGadget(const T a,
                                                           const T b,
                                                           const T a_min,
                                                           const T b_min,
                                                           CVC4::prop::CnfStream* cnf) {
  Unreachable();
}

template<class T>
std::pair<T, std::pair<T, T> > inline optimalSMinGadget(const T a,
                                                        const T b,
                                                        CVC4::prop::CnfStream* cnf) {
  Unreachable();
}



template<class T>
void inline optimalSMin(const std::vector<T>& a,
                        const std::vector<T>& b,
                        std::vector<T>& bits,
                        CVC4::prop::CnfStream* cnf) {
  Unreachable();
}

std::pair<Node, std::pair <Node, Node> >
optimalMaxGadget(const Node a, const Node b,
                 const Node a_max, const Node b_max,
                 CVC4::prop::CnfStream* cnf);

std::pair<Node, std::pair<Node, Node> >
optimalSMaxGadget(const Node a,
                  const Node b,
                  CVC4::prop::CnfStream* cnf);

void optimalSMax(const std::vector<Node>& a,
                 const std::vector<Node>& b,
                 std::vector<Node>& bits,
                 CVC4::prop::CnfStream* cnf);

std::pair<Node, std::pair <Node, Node> >
optimalMinGadget(const Node a, const Node b,
                 const Node a_min, const Node b_min,
                 CVC4::prop::CnfStream* cnf);

std::pair<Node, std::pair<Node, Node> >
optimalSMinGadget(const Node a,
                  const Node b,
                  CVC4::prop::CnfStream* cnf);

void optimalSMin(const std::vector<Node>& a,
                 const std::vector<Node>& b,
                 std::vector<Node>& bits,
                 CVC4::prop::CnfStream* cnf);


}
}
}
#endif // __CVC4__GENERATED__ENCODINGS_H
