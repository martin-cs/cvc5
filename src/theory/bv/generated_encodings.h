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

/******************************
* Reference encodings   
*    
*****************************/
template <class T>
inline void shiftOptimalAddMultiplier(const std::vector<T>&a, const std::vector<T>&b,
				      std::vector<T>& res, CVC4::prop::CnfStream* cnf);

  
template <class T>
T inline optimalUltGadget (const T &a, const T &b, const T &rest,
			      CVC4::prop::CnfStream* cnf) {
  T eq = mkIff(a,b);
  return mkIte(eq, rest, mkNot(a));
}
 
template <class T>
T inline optimalSignGadget (const T& a, const T& b, const T &aLTbRec,
			      CVC4::prop::CnfStream* cnf) {
  // an and bn are the most significant bits
  // aLTb is the variable representing ULT(a[n-2:0], b[n-2:0])

  T neg_pos = mkAnd(a, mkNot(b));
  T aEQb = mkIff(a,b);
  T res = mkOr(neg_pos,
	       (mkAnd(aEQb,
		      aLTbRec)));
  return res;
}

template <class T>
std::pair<T,T> inline optimalFullAdder(const T a, const T b, const T cin,
                                       CVC4::prop::CnfStream* cnf) {
  Unreachable();
}

template <class T>
inline void optimalMult2(const std::vector<T>&a,
			 const std::vector<T>& b,
			 std::vector<T>& c,
			 prop::CnfStream* cnf) {
  Unreachable();
}

template <class T>
inline void mult2(const std::vector<T>&a,
		  const std::vector<T>& b,
		  std::vector<T>& c,
		  prop::CnfStream* cnf) {
  Assert (a.size() == b.size() && a.size() == 2);
  std::vector<T> zeroes_a(a.size(), mkFalse<T>());
  std::vector<T> zeroes_b(a.size(), mkFalse<T>());
  zeroes_a.insert(zeroes_a.begin(), a.begin(), a.end());
  zeroes_b.insert(zeroes_b.begin(), b.begin(), b.end());
  shiftOptimalAddMultiplier(zeroes_a, zeroes_b, c, cnf);
}
 
 
template <class T>
inline void optimalMult3(const std::vector<T>&a,
			 const std::vector<T>& b,
			 std::vector<T>& c, prop::CnfStream* cnf) {
  Unreachable();
}

template <class T>
inline void mult3(const std::vector<T>&a,
			 const std::vector<T>& b,
			 std::vector<T>& c, prop::CnfStream* cnf) {
  Assert (a.size() == b.size() && a.size() == 3);
  std::vector<T> zeroes_a(a.size(), mkFalse<T>());
  std::vector<T> zeroes_b(a.size(), mkFalse<T>());
  zeroes_a.insert(zeroes_a.begin(), a.begin(), a.end());
  zeroes_b.insert(zeroes_b.begin(), b.begin(), b.end());
  shiftOptimalAddMultiplier(zeroes_a, zeroes_b, c, cnf);
}
 
 
template <class T>
inline void optimalMult4(const std::vector<T>&a,
			 const std::vector<T>& b,
			 std::vector<T>& c, prop::CnfStream* cnf) {
  Unreachable();
  // FIXME: until we have the real encoding for debugging
  Assert (a.size() == b.size() && a.size() == 4);
  std::vector<T> zeroes_a(a.size(), mkFalse<T>());
  std::vector<T> zeroes_b(a.size(), mkFalse<T>());
  zeroes_a.insert(zeroes_a.begin(), a.begin(), a.end());
  zeroes_b.insert(zeroes_b.begin(), b.begin(), b.end());
  shiftOptimalAddMultiplier(zeroes_a, zeroes_b, c, cnf);
}
 
/******************************
* Generated encodings   
*    
*****************************/
template<class T>
void optimalMult2Aux(const std::vector<T>&a,
			    const std::vector<T>& b,
			    std::vector<T>& c, prop::CnfStream* cnf);
template<class T>
void optimalMult3Aux(const std::vector<T>&a,
			    const std::vector<T>& b,
			    std::vector<T>& c, prop::CnfStream* cnf);
template<class T>
void optimalMult4Aux(const std::vector<T>&a,
			    const std::vector<T>& b,
			    std::vector<T>& c, prop::CnfStream* cnf);
 

 
std::pair<Node, Node> optimalFullAdder(const Node a, const Node b, const Node cin,
					      CVC4::prop::CnfStream* cnf);
 
template <>
Node optimalUltGadget(const Node &a, const Node &b, const Node &rest,
		      CVC4::prop::CnfStream* cnf);

template<>
Node optimalSignGadget(const Node& a, const Node& b, const Node &aLTb,
			      CVC4::prop::CnfStream* cnf);

template<>
void optimalMult2(const std::vector<Node>&a,
			 const std::vector<Node>& b,
			 std::vector<Node>& c, prop::CnfStream* cnf);

template<>
void optimalMult3(const std::vector<Node>&a,
			 const std::vector<Node>& b,
			 std::vector<Node>& c, prop::CnfStream* cnf);
template<>
void optimalMult4(const std::vector<Node>&a,
			 const std::vector<Node>& b,
			 std::vector<Node>& c, prop::CnfStream* cnf);
template<>
void optimalMult2Aux(const std::vector<Node>&a,
			    const std::vector<Node>& b,
			    std::vector<Node>& c, prop::CnfStream* cnf);
template<>
void optimalMult3Aux(const std::vector<Node>&a,
			    const std::vector<Node>& b,
			    std::vector<Node>& c, prop::CnfStream* cnf);
template<>
void optimalMult4Aux(const std::vector<Node>&a,
			    const std::vector<Node>& b,
			    std::vector<Node>& c, prop::CnfStream* cnf);
 

/*****************************
*
* Helper functions that combine the optimal primitives
* 
******************************/

 
template <class T>
T optimalRippleCarryAdder(const std::vector<T>&a, const std::vector<T>& b, std::vector<T>& res, T carry, prop::CnfStream* cnf) {
  Unreachable();
  return carry;
}

Node inline optimalRippleCarryAdder(const std::vector<Node>&av,
                                    const std::vector<Node>& bv,
                                    std::vector<Node>& res, Node cin, prop::CnfStream* cnf) {
  Assert (av.size() == bv.size() &&res.size() == 0);
  Node carry = cin;
  std::pair<Node, Node> fa_res;
  for (unsigned i = 0 ; i < av.size(); ++i) {
    Node a = av[i];
    Node b = bv[i];
    fa_res = optimalFullAdder(a, b, carry, cnf);
    
    carry = fa_res.second;
    res.push_back(fa_res.first);
  }

  return carry;
}

 
template <class T>
T inline optimalUltBB(const std::vector<T>&a, const std::vector<T>& b,
		      unsigned k, bool orEqual, CVC4::prop::CnfStream* cnf) {
  Assert (a.size() && b.size());
  Assert (k <= a.size());
  
  T answer = orEqual? mkTrue<T>() : mkFalse<T>();
  for (int i = 0; i < k; ++i) {
    answer = optimalUltGadget(a[i], b[i], answer, cnf);
  }
  return answer;
}

template <class T>
void shiftOptimalAddMultiplier(const std::vector<T>&a, const std::vector<T>& b,
			       std::vector<T>& res, CVC4::prop::CnfStream* cnf) {
  Unreachable();
}

template<> 
inline void shiftOptimalAddMultiplier(const std::vector<Node>&a, const std::vector<Node>&b,
				      std::vector<Node>& res, CVC4::prop::CnfStream* cnf) {
  
  for (unsigned i = 0; i < a.size(); ++i) {
    res.push_back(mkAnd(b[0], a[i])); 
  }

  for(unsigned k = 1; k < res.size(); ++k) {
    Node carry_in = mkFalse<Node>();
    std::pair<Node, Node> fa_res;
    for(unsigned j = 0; j < res.size() -k; ++j) {
      Node aj = mkAnd(b[k], a[j]);
      fa_res = optimalFullAdder(res[j+k], aj, carry_in, cnf);
      res[j+k] = fa_res.first;
      carry_in = fa_res.second;
    }
  }
}
template <class T>
inline void optimalMultKBottom(const std::vector<T>& a, const std::vector<T>& b,
			       std::vector<T>& c, unsigned k, CVC4::prop::CnfStream* cnf) {
  Unreachable();
}

template<>
inline void optimalMultKBottom(const std::vector<Node>& a, const std::vector<Node>& b,
			       std::vector<Node>& res, unsigned k, CVC4::prop::CnfStream* cnf) {
  Assert (k == 3 || k == 4 || k == 2); // only optimal encodings implemented so far
  Assert (k <= a.size());
  std::vector<Node> a_bottom;
  std::vector<Node> b_bottom;
  for (unsigned i = 0; i < k; ++i) {
    a_bottom.push_back(a[i]);
    b_bottom.push_back(b[i]);
  }
  
  std::vector<Node> bottom_mult;
  if (k == 2) {
    optimalMult2(a_bottom, b_bottom, bottom_mult, cnf);
  } else if (k == 3) {
    optimalMult3(a_bottom, b_bottom, bottom_mult, cnf);
  } else if (k == 4) {
    optimalMult4(a_bottom, b_bottom, bottom_mult, cnf);
  }

  Assert(bottom_mult.size() == 2*k);

  unsigned width = a.size();

  // Computing the n-k width sum of a[n-1:k]^b[j] where j ranges from 0...k-1
  std::vector<Node> ksum;
  for (unsigned i = k; i < a.size(); ++i) {
    ksum.push_back(mkAnd(b[0], a[i])); 
  }
  
  std::pair<Node, Node> fa_res;
  for (unsigned i = 1; i < std::min(width -k, k); ++i) {
    Node carry_in = mkFalse<Node>();
    for (unsigned j = k; j < width - i; ++j) {
      Node aj = mkAnd(b[i], a[j]);
      fa_res = fullAdder(ksum[j+i-k], aj, carry_in);
      ksum[j+i-k] = fa_res.first;
      carry_in = fa_res.second;
    }
  }
  // concatenate ksum with the bottom k of bottom_mult (no overlap)
  for (unsigned i = 0; i < k; ++i) {
    res.push_back(bottom_mult[i]);
  }
  res.insert(res.end(), ksum.begin(), ksum.end());
  Assert (res.size() == a.size());
  // now add top k bits of bottom_mult
  Node carry = mkFalse<Node>();

  // zero extend or truncate bottom_mult to match size
  bottom_mult.resize(a.size(), mkFalse<Node>());
  
  for (unsigned i = k; i < bottom_mult.size(); ++i) {
    fa_res = fullAdder(res[i], bottom_mult[i], carry);
    res[i] = fa_res.first;
    carry = fa_res.second;
  }

  // finally add the rest of the circuit
  for(unsigned i = k; i < res.size(); ++i) {
    carry = mkFalse<Node>();
    for(unsigned j = 0; j < res.size() -i; ++j) {
      Node aj = mkAnd(a[j], b[i]);
      fa_res = fullAdder(res[j+i], aj, carry);
      res[j+i] = fa_res.first;
      carry = fa_res.second;
    }
  }
  res.resize(a.size());
}

typedef std::vector<Node> Block;
// multiplies the bottom length bits of a with b in base 4
inline Node multByBlock2(const std::vector<Node>& a, const Block& block_b,
			 std::vector<Node>& res, unsigned length, CVC4::prop::CnfStream* cnf) {
  Assert (a.size() >= 2 && length % 2 == 0);

  Block carry_in(4, mkFalse<Node>());
  Block curr_sum, curr;
  
  for (unsigned i = 0; i < length; i +=2) {
    Block block_a(2);
    block_a[0] = a[i];
    block_a[1] = a[i+1];
    // curr will have bitwidth 4 so half of it is carry other half result
    if (options::bvBlock2MultOpt()) {
      optimalMult2<Node>(block_a, block_b, curr, cnf);
    } else {
      mult2<Node>(block_a, block_b, curr, cnf);
    }
    // make sure to add the carry in 
    rippleCarryAdder(curr, carry_in, curr_sum, mkFalse<Node>());
    
    res.push_back(curr_sum[0]);
    res.push_back(curr_sum[1]);
    
    carry_in[0] = curr_sum[2];
    carry_in[1] = curr_sum[3];

    curr_sum.clear();
    curr.clear();
  }
  bool odd = a.size() % 2;
  if (odd) {
    Node c = fullAdder(mkAnd(a[length], block_b[0]),
		       carry_in[0], mkFalse<Node>()).first;
    return c;
  }
  return carry_in[0];
}

template<class T>
inline void optimalBlock2Mult(const std::vector<T>& a, const std::vector<T>& b,
			      std::vector<T>& res, CVC4::prop::CnfStream* cnf) {
  Unreachable();
}
 
 
// TODO use different gadget to add the odd part
inline void optimalBlock2Mult(const std::vector<Node>& a, const std::vector<Node>& b,
			      std::vector<Node>& res, CVC4::prop::CnfStream* cnf) {
  Assert (a.size() >= 2);
  bool odd_bw = a.size() % 2;
  unsigned even_width = odd_bw ? a.size() - 1: a.size();
  
  Block block_b(2);
  block_b[0] = b[0];
  block_b[1] = b[1];
  Node carry = multByBlock2(a, block_b, res, even_width, cnf);
  if (odd_bw) res.push_back(carry);
  
  Assert (res.size() == a.size());

  std::pair<Node, Node> fa_res;
  for(unsigned i = 2; i < even_width; i+=2) {
    block_b[0] = b[i];
    block_b[1] = b[i+1];

    std::vector<Node> ai_vec;
    carry = multByBlock2(a, block_b, ai_vec, even_width - i, cnf);
    if (odd_bw) ai_vec.push_back(carry);

    Assert (ai_vec.size() == a.size() - i);
    // use regular adder to add to rest
    Node carry_in = mkFalse<Node>();
    for(unsigned j = 0; j < res.size() - i; ++j) {
      Node aj = ai_vec[j];
      fa_res = fullAdder(res[j+i], aj, carry_in);
      res[j+i] = fa_res.first;
      carry_in = fa_res.second;
    }
  }
  // add last bit if it's odd
  if (odd_bw) {
    res[even_width] = fullAdder(res[even_width],
				mkAnd(b[even_width], a[0]),
				mkFalse<Node>()).first;
  }
}

/*************** DEBUGGING REFERENCE ENCODINGS ***********************/

void optimalMult2Debug(const std::vector<Node>&a,
			      const std::vector<Node>& b,
			      std::vector<Node>& c, prop::CnfStream* cnf);
void optimalMult3Debug(const std::vector<Node>&a,
			      const std::vector<Node>& b,
			      std::vector<Node>& c, prop::CnfStream* cnf);
 
void optimalMult4Debug(const std::vector<Node>&a,
			      const std::vector<Node>& b,
			      std::vector<Node>& c, prop::CnfStream* cnf);
 
}
}
}

#endif
