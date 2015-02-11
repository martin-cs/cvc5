/*********************                                                        */
/*! \file encoding_experiments.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
**/

#include "encoding/encoding_experiments.h"
#include "expr/node.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/bv/bitblaster_template.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "main/options.h"

#include <stdlib.h>

using namespace CVC4;
using namespace CVC4::prop;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

// fixed are literals that represent the fixed values of the bits
// according to some heuristic
void selectBits(Options& opts, std::vector<int>& fixed) {
  unsigned  num_bits = opts[options::encodingNumFixed];
  unsigned width = opts[options::encodingBitwidth];
  std::vector<bool> picked(width, false);

  for (unsigned i = 0; i < num_bits; ++i) {
    unsigned nbit;
    do {
      nbit = rand() % width;
    } while (picked[nbit]);
    picked[nbit] = true;
    nbit = rand() % 2 ? -nbit : nbit;
    fixed.push_back(nbit);
  }
  Assert (fixed.size() == num_bits);
}

void fixBits(EncodingBitblaster::Bits& bits, std::vector<int>& fixed, std::vector<Node>& assumps) {
  for (unsigned i = 0; i < fixed.size(); ++i) {
    int n = fixed[i] < 0 ? - fixed[i] : fixed[i];
    Node bit =fixed[i] < 0 ? utils::mkNot(bits[n]) : bits[n];
    assumps.push_back(bit);
  }
}

void CVC4::runEncodingExperiment(Options& opts) {
  ExprManager em;
  SmtEngine smt(&em);
  smt::SmtScope scope(&smt);
  std::cout << "Running encoding experiments " << std::endl; 
  // NodeManager* nm = NodeManager::currentNM();
  unsigned width = opts[options::encodingBitwidth];

  Node a = utils::mkVar(width);
  Node b = utils::mkVar(width);
  Node c = utils::mkVar(width);

  Node a_plus_b = utils::mkNode(kind::BITVECTOR_PLUS, a, b);
  Node eq = utils::mkNode(kind::EQUAL, a_plus_b, c);
  
  
  context::Context* ctx = new context::Context();

  EncodingBitblaster bb1(ctx, "default-plus");
  CnfStream* cnf1 = bb1.getCnfStream();
  bb1.setTermBBStrategy(kind::BITVECTOR_PLUS, DefaultPlusBB<Node>);
  
  EncodingBitblaster bb2(ctx, "optimal-plus");
  CnfStream* cnf2 = bb2.getCnfStream();
  bb2.setTermBBStrategy(kind::BITVECTOR_PLUS, OptimalPlusBB<Node>);

  EncodingBitblaster::EncodingNotify en1(cnf2, &bb1);
  bb1.setNotify(&en1);
  EncodingBitblaster::EncodingNotify en2(cnf1, &bb2);
  bb2.setNotify(&en2);

  bb1.assertFact(eq);
  bb2.assertFact(eq);

 
  EncodingBitblaster::Bits a1_bits, b1_bits, c1_bits;
  bb1.getBBTerm(a, a1_bits);
  bb1.getBBTerm(b, b1_bits);
  bb1.getBBTerm(c, c1_bits);

  EncodingBitblaster::Bits a2_bits, b2_bits, c2_bits;
  bb2.getBBTerm(a, a2_bits);
  bb2.getBBTerm(b, b2_bits);
  bb2.getBBTerm(c, c2_bits);
  
  for (unsigned i = 0; i < opts[options::encodingNumIterations]; ++i) {
    std::cout << "RUNNING iteration " << i << std::endl;
    ctx->push();
    std::vector<int> a_fixed, b_fixed, c_fixed;
    std::vector<Node> assumps1, assumps2;
    
    selectBits(opts, a_fixed);
    selectBits(opts, b_fixed);
    selectBits(opts, c_fixed);
    
     // select what bits to fix
    fixBits(a1_bits, a_fixed, assumps1);
    fixBits(b1_bits, b_fixed, assumps1);
    fixBits(c1_bits, c_fixed, assumps1);

    fixBits(a2_bits, a_fixed, assumps2);
    fixBits(b2_bits, b_fixed, assumps2);
    fixBits(c2_bits, c_fixed, assumps2);

    Assert (assumps1.size() == assumps2.size()); 

    Debug("encoding") << "Fixed bits "<< std::endl;
    for (unsigned i = 0; i < assumps1.size(); ++i) {
      Debug("encoding") << "   " << assumps1[i] << std::endl; 
      bb1.assumeLiteral(assumps1[i]);
      bb2.assumeLiteral(assumps2[i]);
    }

    // bool res1 = bb1.solve();
    // bool res2 = bb2.solve();
    Debug("encoding") << "  Propagating " << bb1.getName() << std::endl;
    bool res1 = bb1.propagate();
    Debug("encoding") << "      res = "<< res1 << std::endl;

    Debug("encoding") << "  Propagating " << bb2.getName() << std::endl;
    bool res2 = bb2.propagate();
    Debug("encoding") << "      res = "<< res2 << std::endl;

    unsigned en1_unique = 0;
    unsigned both = 0;
    for (TNodeSet::const_iterator it = en1.begin(); it != en1.end(); ++it) {
      if (en2.isPropagated(*it)) {
	++both; 
      } else {
	++en1_unique;
      }
    }

    unsigned en2_unique = 0;
    for (TNodeSet::const_iterator it = en2.begin(); it != en2.end(); ++it) {
      if (! en1.isPropagated(*it)) {
	++en2_unique;
      }
    }

    std::cout << "  Both propagate " << both << std::endl;
    std::cout << "  " << bb1.getName() << " unique propagate # " << en1_unique << std::endl;
    std::cout << "  " << bb1.getName() << " total propagations # " << en1.d_numTotalPropagations << std::endl;
    std::cout << "  " << bb1.getName() << " shared propagations # " << en1.d_numSharedPropagations << std::endl;
										  
    std::cout << "  " << bb2.getName() << " unique propagate # " << en2_unique << std::endl;
    std::cout << "  " << bb2.getName() << " total propagations # " << en2.d_numTotalPropagations << std::endl;
    std::cout << "  " << bb2.getName() << " shared propagations # " << en2.d_numSharedPropagations << std::endl;

    // call solve to ensure that the encodings are correct
    res1 = res1 ? bb1.solve() : res1;
    std::cout << "  " << bb1.getName() <<" full solve result " << res1 << std::endl;
    res2 = res2 ? bb2.solve() : res2;
    std::cout << "  " << bb2.getName() <<" full solve result " << res2 << std::endl;
    
    // Node a_model = bb1.getModelFromSatSolver(a, false);
    // Node b_model = bb1.getModelFromSatSolver(b, false);
    // Node c_model = bb1.getModelFromSatSolver(c, false);

    // std::cout << a << " => " << a_model << std::endl;
    // std::cout << b << " => " << b_model << std::endl;
    // std::cout << c << " => " << c_model << std::endl;
    
    Assert( res1 == res2);
    en1.clear();
    en2.clear();
    ctx->pop();
    // print statistics
  }
  
  delete ctx;
}
