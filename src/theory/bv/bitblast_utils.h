/*********************                                                        */
/*! \file bitblast_utils.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Various utility functions for bit-blasting.
 **
 ** Various utility functions for bit-blasting.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BITBLAST__UTILS_H
#define __CVC4__BITBLAST__UTILS_H


#include <ostream>
#include "expr/node.h"

#ifdef CVC4_USE_ABC
#include "base/main/main.h"
#include "base/abc/abc.h"


extern "C" {
#include "sat/cnf/cnf.h"
}
#endif

namespace CVC4 {

namespace theory {
namespace bv {

template <class T> class TBitblaster;

template <class T> 
std::string toString (const std::vector<T>& bits);

template <> inline
std::string toString<Node> (const std::vector<Node>& bits) {
  std::ostringstream os;
  for (int i = bits.size() - 1; i >= 0; --i) {
    TNode bit = bits[i];
    if (bit.getKind() == kind::CONST_BOOLEAN) {
      os << (bit.getConst<bool>() ? "1" : "0");
    } else {
      os << bit<< " ";
    }
  }
  os <<"\n";
  return os.str();
} 

template <class T> T mkTrue(); 
template <class T> T mkFalse(); 
template <class T> T mkNot(T a);
template <class T> T mkOr(T a, T b);
template <class T> T mkOr(const std::vector<T>& a);
template <class T> T mkAnd(T a, T b);
template <class T> T mkAnd(const std::vector<T>& a);
template <class T> T mkXor(T a, T b);
template <class T> T mkIff(T a, T b);
template <class T> T mkIte(T cond, T a, T b);


template <> inline
Node mkTrue<Node>() {
  return NodeManager::currentNM()->mkConst<bool>(true);
}

template <> inline
Node mkFalse<Node>() {
  return NodeManager::currentNM()->mkConst<bool>(false);
}

template <> inline
Node mkNot<Node>(Node a) {
  return NodeManager::currentNM()->mkNode(kind::NOT, a);
}

template <> inline
Node mkOr<Node>(Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::OR, a, b);
}

template <> inline
Node mkOr<Node>(const std::vector<Node>& children) {
  Assert (children.size());
  if (children.size() == 1)
    return children[0]; 
  return NodeManager::currentNM()->mkNode(kind::OR, children); 
}


template <> inline
Node mkAnd<Node>(Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::AND, a, b);
}

template <> inline
Node mkAnd<Node>(const std::vector<Node>& children) {
  Assert (children.size());
  if (children.size() == 1)
    return children[0]; 
  return NodeManager::currentNM()->mkNode(kind::AND, children); 
}


template <> inline
Node mkXor<Node>(Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::XOR, a, b);
}

template <> inline
Node mkIff<Node>(Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::IFF, a, b);
}

template <> inline
Node mkIte<Node>(Node cond, Node a, Node b) {
  return NodeManager::currentNM()->mkNode(kind::ITE, cond, a, b);
}

/*
 Various helper functions that get called by the bitblasting procedures
 */

template <class T>
void inline extractBits(const std::vector<T>& b, std::vector<T>& dest, unsigned lo, unsigned hi) {
  Assert ( lo < b.size() && hi < b.size() && lo <= hi);
  for (unsigned i = lo; i <= hi; ++i) {
    dest.push_back(b[i]); 
  }
}

template <class T>
void inline negateBits(const std::vector<T>& bits, std::vector<T>& negated_bits) {
  for(unsigned i = 0; i < bits.size(); ++i) {
    negated_bits.push_back(mkNot(bits[i])); 
  }
}

template <class T>
bool inline isZero(const std::vector<T>& bits) {
  for(unsigned i = 0; i < bits.size(); ++i) {
    if(bits[i] != mkFalse<T>()) {
      return false; 
    }
  }
  return true; 
}
 
template <class T>
void inline rshift(std::vector<T>& bits, unsigned amount) {
  for (unsigned i = 0; i < bits.size() - amount; ++i) {
    bits[i] = bits[i+amount]; 
  }
  for(unsigned i = bits.size() - amount; i < bits.size(); ++i) {
    bits[i] = mkFalse<T>(); 
  }
}

template <class T>
void inline lshift(std::vector<T>& bits, unsigned amount) {
  for (int i = (int)bits.size() - 1; i >= (int)amount ; --i) {
    bits[i] = bits[i-amount]; 
  }
  for(unsigned i = 0; i < amount; ++i) {
    bits[i] = mkFalse<T>(); 
  }
}

template <class T>
void inline makeZero(std::vector<T>& bits, unsigned width) {
  Assert(bits.size() == 0); 
  for(unsigned i = 0; i < width; ++i) {
    bits.push_back(mkFalse<T>()); 
  }
}

template <class T>
std::pair<T,T> inline fullAdder(const T a, const T b, const T cin) {
  T cout = mkOr(mkAnd(a, b),
		mkAnd(mkXor(a, b),
		      cin));;
  T sum = mkXor(mkXor(a, b), cin);
  return std::make_pair(sum, cout);
}

 
/** 
 * Constructs a simple ripple carry adder
 * 
 * @param a first term to be added
 * @param b second term to be added
 * @param res the result
 * @param carry the carry-in bit 
 * 
 * @return the carry-out
 */
template <class T>
T inline rippleCarryAdder(const std::vector<T>&a, const std::vector<T>& b,
			  std::vector<T>& res, T cin) {
  Assert(a.size() == b.size() && res.size() == 0);

  T sum;
  T carry = cin;
  std::pair<T, T> fa_res;
  for (unsigned i = 0 ; i < a.size(); ++i) {
    fa_res = fullAdder(a[i], b[i], carry);
    sum = fa_res.first;
    carry = fa_res.second;
    res.push_back(sum); 
  }

  return carry;
}

 
template <class T>
inline void shiftAddMultiplier(const std::vector<T>&a, const std::vector<T>&b, std::vector<T>& res) {
  
  for (unsigned i = 0; i < a.size(); ++i) {
    res.push_back(mkAnd(b[0], a[i])); 
  }
  
  for(unsigned k = 1; k < res.size(); ++k) {
    T carry_in = mkFalse<T>();
    std::pair<T, T> fa_res;
    for(unsigned j = 0; j < res.size() -k; ++j) {
      T aj = mkAnd(a[j], b[k]);
      fa_res = fullAdder(res[j+k], aj, carry_in);
      res[j+k] = fa_res.first;
      carry_in = fa_res.second;
    }
  }
}
 

template <class T>
T inline uLessThanBB(const std::vector<T>&a, const std::vector<T>& b, bool orEqual) {
  Assert (a.size() && b.size());
  
  T res = orEqual? mkTrue<T>() : mkFalse<T>();
  
  for (unsigned i = 0; i < a.size(); ++i) {
    res = mkIte(mkIff(a[i], b[i]), res, mkNot(a[i]));
  }
 return res;
}
 
template <class T>
T inline sLessThanBB(const std::vector<T>&a, const std::vector<T>& b, bool orEqual) {
  Assert (a.size() && b.size());
  if (a.size() == 1) {
    if(orEqual) {
      return  mkOr(mkIff(a[0], b[0]),
                   mkAnd(a[0], mkNot(b[0]))); 
    }

    return mkAnd(a[0], mkNot(b[0]));
  }
  unsigned n = a.size() - 1; 
  std::vector<T> a1, b1;
  extractBits(a, a1, 0, n-1);
  extractBits(b, b1, 0, n-1);
  
  // unsigned comparison of the first n-1 bits
  T ures = uLessThanBB(a1, b1, orEqual);
  T res = mkOr(// a b have the same sign
               mkAnd(mkIff(a[n], b[n]),
                     ures),
               // a is negative and b positive
               mkAnd(a[n],
                     mkNot(b[n])));
  return res;
}

 
}
}
}




/* typedef enum _fullAdderEncoding {  */
/*   /\** Operation based **\/ */
/*   TSEITIN_NAIVE_AB_CIRCUIT,     // Original CBMC */
/*   TSEITIN_NAIVE_AC_CIRCUIT, */
/*   TSEITIN_NAIVE_BC_CIRCUIT, */
/*   TSEITIN_SHARED_AB_CIRCUIT, */
/*   TSEITIN_SHARED_AC_CIRCUIT, */
/*   TSEITIN_SHARED_BC_CIRCUIT, */
/*   AIG_NAIVE_AB_CIRCUIT,         // Probably the worst... */
/*   AIG_NAIVE_AC_CIRCUIT, */
/*   AIG_NAIVE_BC_CIRCUIT, */
/*   AIG_SHARED_AB_CIRCUIT,        // CVC4 */
/*   AIG_SHARED_AC_CIRCUIT, */
/*   AIG_SHARED_BC_CIRCUIT, */
  
/*   /\** Mixed **\/ */
/*   DANIEL_COMPACT_CARRY,      // CBMC old default */
  
/*   /\** Clause based **\/ */
/*   MINISAT_SUM_AND_CARRY, */
/*   MINISAT_COMPLETE,          // With the 6 additional clauses */
/*   MARTIN_OPTIMAL             // Current CBMC */
/* } fullAdderEncoding; */


/* template <class T> std::vector<T> inline fullAdder (const fullAdderEncoding &fullAdderstyle, const T &a, const T &b, const T&c) { */
/*   // result[0] is sum */
/*   // result[1] is carry */
  
/*   Unimplemented("Need to connect up"); */
/* } */

/* typedef enum _halfAdderEncoding { */
/*   // How many others are there... */
/*   DEFAULT */
/*   // \todo optimal half_adder */
/* } halfAdderEncoding; */

/* template <class T> std::vector<T> inline halfAdder (const halfAdderEncoding &hlafAdderStyle, const T &a, const T &b) { */
/*   Unimplemented("Need to connect up"); */
/* } */


/* struct add2Encoding { */
/*   fullAdderEncoding fullAdderStyle; */
/*   size_t carrySelectMinimum; */
/*   size_t carrySelectSplit; */
/*   enum { */
/*     RIPPLE_CARRY,         // A common default */
/*     CARRY_LOOKAHEAD */
/*   } style; */
/* }; */



/* template <class T> std::vector<T> inline add2 (const add2Encoding &add2Style, const std::vector<T> &a, const std::vector<T> &b, const T &cin) { */
/*   Assert(a.length() == b.length()); */
/*   std::vector result(a.length() + 1); */

/*   if (a.length() > add2Style.carrySelectMinimum) { */
/*       Unimplemented("Carry select unimplemented"); */
/*   } else { */

/*     switch (add2Style.style) { */
/*     case RIPPLE_CARRY : */
/*       { */
/* 	T carry = cin; */
/* 	std::vector<T> tmp; */
/* 	for (int i = 0; i < a.length(); ++i) { */
/* 	  tmp = fullAdder(add2Style.fullAdderStyle, a[i], b[i], carry); */
/* 	  result[i] =  tmp[0]; */
/* 	  carry = tmp[1]; */
/* 	} */
/* 	result[a.length()] = carry; */
/*       } */
/*       break; */

/*     case CARRY_LOOKAHEAD : */
/*     default : */
/*       Unimplemented("Add2 style not implemented"); */
/*     } */

/*   } */

/*   Assert(result.length() == a.length() + 1); */
/*   return result; */
/* } */

/* struct add3Encoding { */
/*   fullAdderEncoding fullAdderStyle; */
/*   add2Encoding add2Style; */
/*   enum { */
/*     // \todo Optimal add3 */
/*     THREE_TO_TWO_THEN_ADD */
/*   } style; */
/* }; */

/* template <class T> std::vector<T> inline add3 (const add3Encoding &add3Style, const std::vector<T> &a, const std::vector<T> &b, const std::vector<T> &c, const T &cin) { */
/*   Assert(a.length() == b.length()); */
/*   Assert(a.length() == c.length()); */
/*   std::vector result(); */

/*   switch (add3Style.style) { */
/*   case THREE_TO_TWO_THEN_ADD : */
/*     { */
/*       std::vector<T> sum(a.length() + 1); */
/*       std::vector<T> carry(a.length() + 1); */

/*       carry[0] = cin; */

/*       std::vector<T> tmp; */
/*       for (int i = 0; i < a.length(); ++i) { */
/* 	tmp = fullAdder(a[i], b[i], c[i]); */
/* 	sum[i] = tmp[0]; */
/* 	carry[i + 1] = tmp[1]; */
/*       } */

/*       sum[a.length()] = mkFalse(); */

/*       // \todo We can add in a second carry here... */
/*       result = add2(add3Style.add2Style, sum, carry, mkFalse()); */

/*     } */
/*     break; */
/*   default :  */
/*     Unimplemented("Add3 style not implemented"); */
/*   } */

/*   Assert(result.length() == a.length() + 2); */
/*   return result; */
/* } */


/* struct accumulateEncoding { */
/*   add2Encoding add2Style; */
/*   add3Encoding add3Style; */

/*   enum { */
/*     LINEAR_FORWARDS,    // Most solvers */
/*     LINEAR_BACKWARDS, */
/*     TREE_REDUCTION, */

/*     ADD3_LINEAR_FORWARDS, */
/*     ADD3_LINEAR_BACKWARDS, */
/*     ADD3_TREE */
/*   } style; */
/* }; */

/* template <class T> std::vector<T> inline accumulate (const accumulateEncoding &accumulateStyle, const std::vector<std::vector<T> > &set) { */
/*   size_t inputCount = set.length(); */
/*   size_t inputLength = set[0].length(); */

/*   assert(inputCount != 0); */
/*   for (i = 0; i < inputCount; ++i) { */
/*     assert(set[i].length() == inputLength); */
/*   } */

/*   if (inputCount == 1) { */
/*     return set[0]; */
/*   } */

/*   std::vector<T> sum; */

/*   switch (accumulateEncoding.style) { */
/*   case LINEAR_FORWARDS : */
/*     { */
/*       sum = set[0]; */

/*       for (int i = 1; i < inputCount; ++i) { */
/* 	// \todo We can sneak in lots of carrys in accumulation... */
/* 	sum = add2(accumulateStyle.add2Style, sum, extend(set[i], sum.length() - set[i].length()), mkFalse()); */
/*       } */

/*     } */
/*     break; */

/*   case LINEAR_BACKWARDS : */
/*     { */
/*       sum = set[inputCount - 1]; */

/*       for (int i = inputCount - 2; i >= 0; --i) { */
/* 	sum = add2(accumulateStyle.add2Style, sum, extend(set[i], sum.length() - set[i].length()), mkFalse()); */
/*       } */

/*     } */
/*     break; */

/*   case TREE_REDUCTION : */
/*     std::vector<std::vector<T> > input = set; */
/*     std::vector<std::vector<T> > output; */

/*     while (input.length() >= 2) { */
/*       for (int i = 0; i + 1< input.length(); i += 2) { */
/* 	output.push_back(add2(accumulateStyle.add2Style, input[i], input[i + 1], mkFalse())); */
/*       } */
/*       if ((input.length() & 1) == 1) { */
/* 	output.push_back[extend(input[input.length() - 1], 1)]; */
/*       } */

/*       input = output; */
/*       output.clear(); */
/*     } */

/*     sum = input[0]; */
/*     break; */

/*   case ADD3_LINEAR_FORWARDS : */
/*     { */
/*       sum = set[0]; */

/*       for (int i = 1; i < inputCount; i += 2) { */
/* 	sum = add3(accumulateStyle.add3Style, */
/* 		   sum, */
/* 		   extend(set[i], sum.length() - set[i].length()), */
/* 		   extend(set[i + 1], sum.length() - set[i + 1].length()), */
/* 		   mkFalse()); */
/*       } */
/*       if ((inputCount & 1) == 0) { */
/* 	sum = add2(accumulateStyle.add2Style, */
/* 		   sum, */
/* 		   extend(set[inputCount - 1], sum.length() - set[inputCount - 1].length()), */
/* 		   mkFalse()); */
/*       } */

/*     } */
/*     break; */

/*   case ADD3_LINEAR_BACKWARDS : */
/*     { */
/*       sum = set[inputCount - 1]; */

/*       for (int i = inputCount - 2; i >= 1; i -= 2) { */
/* 	sum = add3(accumulateStyle.add3Style, */
/* 		   sum, */
/* 		   extend(set[i], sum.length() - set[i].length()), */
/* 		   extend(set[i - 1], sum.length() - set[i - 1].length()), */
/* 		   mkFalse()); */
/*       } */
/*       if ((inputCount & 1) == 0) { */
/* 	sum = add2(accumulateStyle.add2Style, */
/* 		   sum, */
/* 		   extend(set[0], sum.length() - set[0].length()), */
/* 		   mkFalse()); */
/*       } */
/*     } */
/*     break; */

/*   case ADD3_TREE_REDUCTION : */
/*     std::vector<std::vector<T> > input = set; */
/*     std::vector<std::vector<T> > output; */

/*     while (input.length() >= 3) { */
/*       int i; */
/*       for (i = 0; i + 2 < input.length(); i+=3) { */
/* 	output.push_back(add3(accumulateStyle.add3Style, */
/* 			      input[i], */
/* 			      input[i + 1], */
/* 			      input[i + 2], */
/* 			      mkFalse())); */
/*       } */
/*       while (i < input.length()) { */
/* 	output.push_back[extend(input[i], 1)]; */
/* 	++i; */
/*       } */

/*       input = output; */
/*       output.clear(); */
/*     } */

/*     if (input.length() == 2) { */
/*       sum = add2(accumulateStyle.add2Style, */
/* 		 input[0], */
/* 		 input[1], */
/* 		 mkFalse()); */
/*     } else { */
/*       sum = input[0]; */
/*     } */

/*     break; */

/*   default : */
/*     Unimplemented("Accumulate style not implemented"); */
/*   } */

/*   // Trim to the correct length */
/*   size_t lengthIncrement = 0; */
/*   while ((1 << lengthIncrement) < inputCount) { */
/*     ++lengthIncrement; */
/*   } */

/*   return trim(sum, inputLength + lengthIncrement); */
/* } */

/* typedef enum _recursiveMultiplicationEncoding { */
/*   DEFAULT, */
/*   KARATSUBA */
/* } recursiveMultiplicationEncoding; */

/* typedef enum _partialProductEncoding { */
/*   CONVENTIONAL, */
/*   BLOCK2_BY_ADDITION, */
/*   BLOCK3_BY_ADDITION, */
/*   BLOCK4_BY_ADDITION, */
/*   BLOCK5_BY_ADDITION, */
/*   BLOCK2_BY_CONSTANT_MULTIPLICATION, */
/*   BLOCK3_BY_CONSTANT_MULTIPLICATION, */
/*   BLOCK4_BY_CONSTANT_MULTIPLICATION, */
/*   BLOCK5_BY_CONSTANT_MULTIPLICATION, */
/*   OPTIMAL_2_BY_2, */
/*   OPTIMAL_3_BY_3, */
/*   OPTIMAL_4_BY_4, */
/*   OPTIMAL_5_BY_5, */
/* } partialProductEncoding; */


/* typedef enum _reductionEncoding { */
/*   /\** Word level reductions **\/ */
/*   WORD_LEVEL, */
  
/*   /\** Bit level reductions **\/ */
/*   WALLACE_TREE,               // Boolector */
/*   DADDA_TREE, */
  
/*   /\** Carry-save reductions **\/ */
/*   // \todo these */
/*   /\* */
/*   UNARY_TO_BINARY_REDUCTION,   // Not sure about how best to use this */
/*   CARRY_SAVE_LINEAR_REDUCTION, // Needs more parameters */
/*   CARRY_SAVE_TREE_REDUCTION    // Needs more parameters */
/*   *\/ */
/* } reductionEncoding; */

/* struct multiplyEncoding { */
/*   size_t recursiveMinimum; */
/*   recursiveMultiplicationEncoding recursionStyle; */
/*   partialProductEncoding partialProductStyle; */
/*   reductionEncoding reductionStyle; */
/*   accumulateEncoding accumulateStyle; */

/*   bool isWordLevelReduction (void) const { */
/*     return this->reductionStyle == WORD_LEVEL; */
/*   } */

/*   bool isBitLevelReduction (void) const { */
/*     return this->reductionStyle == WALLACE_TREE || */
/*       this->reductionStyle == DADDA_TREE; */
/*   } */
/* }; */


/* template <class T> std::vector<T> inline multiply (const multiplyEncoding &multiplyStyle, const std::vector<T> &a, const std::vector<T> &b) { */
/*   Assert(a.length() == b.length()); */

/*   std::vector<T> product; */

/*   if (a.length() > multiplyStyle.recursiveMinimum) { */

/*     size_t splitPoint = a.length() / 2;  // Rounding down... */
/*     std::vector<T> &ah(a.extract(a.length() - 1, splitPoint + 1)); */
/*     std::vector<T> &al(a.extract(splitPoint, 0)); */

/*     std::vector<T> &bh(b.extract(b.length() - 1, splitPoint + 1)); */
/*     std::vector<T> &bl(b.extract(splitPoint, 0)); */

/*     switch (multiplyStyle.recursionStyle) { */
/*     case DEFAULT : */
/*       std::vector<T> hh(multiply(multiplyStyle, ah, bh)); */
/*       std::vector<T> hl(multiply(multiplyStyle, ah, bl)); */
/*       std::vector<T> lh(multiply(multiplyStyle, al, bh)); */
/*       std::vector<T> ll(multiply(multiplyStyle, al, bl)); */

/*       hh.extend(a.length() * 2); */
/*       hl.extend(a.length() * 2); */
/*       lh.extend(a.length() * 2); */
/*       ll.extend(a.length() * 2); */

/*       // \todo : check for off-by-one errors when width is odd */

/*       product = add3(multiplyStyle.accumulateStyle.add3Style, */
/* 		     or(lshift(hh, splitLength * 2), ll), */
/* 		     lshift(hl, splitLength), */
/* 		     lshift(lh, splitLength)).trim(a.length() * 2); */

/*       break; */
/*     case KARATSUBA : */
/*     default : */
/*       Unimplemented("Recursion style unimplemented"); */
/*     }  */
/*   } */




/*   if (multiplyStyle.isWordLevelReduction() || */
/*       multiplyStyle.isBitLevelReduction()) { */

/*     // Generate the grid */
/*     std::vector< std::vector<T> > grid(a.length()); */
/*     size_t blockSize; */
/*     size_t blockEntryWidth; */

/*     switch (multiplyStyle.partialProductStyle) { */
/*     case CONVENTIONAL : */
/*       blockSize = 1; */
/*       for (int i = 0; i < b.length(); ++i) { */
/* 	grid[i] = and(b[i], a); */
/*       } */
/*       break; */

/*     case BLOCK2_BY_ADDITION : blockSize = 2; blockEntryWidth = a.length() + 1; */
/*     case BLOCK3_BY_ADDITION : blockSize = 3; blockEntryWidth = a.length() + 2; */
/*     case BLOCK4_BY_ADDITION : blockSize = 4; blockEntryWidth = a.length() + 2; */
/*     case BLOCK5_BY_ADDITION : blockSize = 5; blockEntryWidth = a.length() + 3; */
/*       // Build blocks */
/*       std::vector< std::vector<T> > block(1 << blockSize); */

/*       block[0] = zero(blockEntryWidth); */
/*       block[1] = a; */
/*       block[2] = lshift(a.extend(1), 1); */
/*       block[3] = add2(multiplyStyle.accumulateStyle.add2Style, */
/* 		      block[1].extend(1), */
/* 		      block[2], */
/* 		      mkFalse()); */
/*       if (blockSize == 2) goto trim; */

/*       block[4] = lshift(a.extend(2), 2); */
/*       block[5] = add2(multiplyStyle.accumulateStyle.add2Style, */
/* 		      block[1].extend(2), */
/* 		      block[4], */
/* 		      mkFalse()); */
/*       block[6] = lshift(block[3].extend(1), 1); */
/*       block[8] = lshift(a.extend(3), 3); */
/*       block[7] = subtract(block[8], block[1]); */

/*       if (blockSize == 3) goto trim; */

/*       Unimplemented("... and so on ..."); */

/*     trim : */
/*       // Set block width */
/*       for (int i = 0; i < block.length(); ++i) { */
/* 	setLength(block[i], blockEntryWidth); */
/*       } */

/*       // Select to build grid */
/*       if (multiplyStyle.partialProductStyle == BLOCK2_BY_ADDITION) { */
/* 	for (int i = 0; i < b.length(); i += 2) { */
/* 	  // \todo This is not optimal! */
/* 	  grid[i / 2] = ite(b[i + 1],  */
/* 			    ite(b[i], block[3], block[2]), */
/* 			    ite(b[i], block[1], block[0])); */
/* 	} */

/* 	Unimplemented("Fix up for when b.length() is odd"); */

/*       } else { */
/* 	Unimplemented("other selects work similarly"); */
/*       } */

/*       break; */
/*     case BLOCK2_BY_CONSTANT_MULTIPLICATION : blockSize = 2; blockEntryWidth = a.length() + 1; */
/*     case BLOCK3_BY_CONSTANT_MULTIPLICATION : blockSize = 3; blockEntryWidth = a.length() + 2; */
/*     case BLOCK4_BY_CONSTANT_MULTIPLICATION : blockSize = 4; blockEntryWidth = a.length() + 2; */
/*     case BLOCK5_BY_CONSTANT_MULTIPLICATION : blockSize = 5; blockEntryWidth = a.length() + 3; */

/*       Unimplemented("Need the multiply by constant function."); */
/*       break; */

/*     case OPTIMAL_2_BY_2 : */
/*     case OPTIMAL_3_BY_3 : */
/*     case OPTIMAL_4_BY_4 : */
/*     case OPTIMAL_5_BY_5 : */
/*       // It is not immediately obvious how to flatten these back into a grid */
/*     default : */
/*       Unimplemented("Unimplemented partial product style"); */
/*     } */


/*     // Now reduce... */

/*     if (multiplyStyle.isWordLevelReduction()) { */
/*       Assert(multiplyStyle.reductionStyle == WORD_LEVEL); */

/*       for (int i = 0; i < grid.length(); ++i) { */
/* 	lshift(grid[i].extend(a.length() * 2 - grid[i].length()), i * blocksize); */
/*       } */

/*       return accumulate(multiplyStyle.accumulateStyle, grid).trim(something); */

/*     } else { */
/*       Assert(multiplyStyle.isBitLevelReduction()); */

/*       std::vector < std::vector<T> > antiDiagonals(a.length() * 2); */

/*       // Load anti-diagonals correctly */
/*       for (int i = 0; i < grid.length(); ++i) { */
/* 	for (int j = 0; j < grid[i].length(); ++j) { */
/* 	  antiDiagonal[i * blocksize + j].push_back(grid[i][j]); */
/* 	} */
/*       } */

/*       // Reduce */
/*       size_t maximumInDiagonal = 0; */
/*       do { */

/* 	// One reduction round */
/* 	for (int i = antiDiagonals.length() - 1 ; i > 0; --i) { */
/* 	  if (antiDiagonal[i].length() >= 3) { // Or maybe 2 ... */

/* 	    std::vector<T> tmp = antiDiagonal[i]; */
/* 	    antiDiagonal[i].clear(); */

/* 	    for (int j = 0; j < tmp.length(); j += 3) { */
/* 	      // Should this be add2Style.fullAdderStyle?  Does it matter? */
/* 	      std::vector<T> result(fullAdder(multiplyStyle.accumulateStyle.add3Style.fullAdderStyle, */
/* 					      tmp[j], */
/* 					      tmp[j+1], */
/* 					      tmp[j+2])); */
/* 	      antiDiagonal[i].push_back(result[0]); */
/* 	      antiDiagonal[i+1].push_back(result[1]); */
				    
/* 	    } */
/* 	    Unimplemented("Half adder if the remainder is two"); */


/* 	    maximumInDiagonal = (maximumInDiagonal < antiDiagonal[i+1].length()) ? */
/* 	      antiDiagonal[i+1].length : maximumInDiagonal;	     */
/* 	  } */

/* 	  maximumInDiagonal = (maximumInDiagonal < antiDiagonal[i].length()) ? */
/* 	    antiDiagonal[i].length : maximumInDiagonal; */
/* 	}  */

/*       } while (maximumInDiagonal > 3);  // Or maybe 2 ... */

/*       Unimplemented("The final add2 or add3"); */

/*     } */

/*   } else { */
/*     Unimplemented("Carry-save not implemented just yet"); */

/*   } */
/* } */


#endif
