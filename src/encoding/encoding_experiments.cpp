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

using namespace std;
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


void printSatVars(EncodingBitblaster& bb, EncodingBitblaster::Bits& bits) {
  for (unsigned i = 0; i < bits.size(); ++i) {
    std::cout << bb.getCnfStream()->getLiteral(bits[i]).toString() << " ";
  }
  std::cout << std::endl;
}

enum EncodingOrder{
  EQUAL =1,
  LESS =2,
  GREATER =3,
  INCOMPARABLE =4
};

EncodingOrder comparePropagations(EncodingBitblaster::EncodingNotify& en1,
				  EncodingBitblaster::EncodingNotify& en2,
				  EncodingBitblaster& bb1, EncodingBitblaster& bb2) {
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

    Debug("encoding-experiment") << "  Both propagate " << both << std::endl;
    Debug("encoding-experiment") << "  " << bb1.getName() << " unique propagate # " << en1_unique << std::endl;
    Debug("encoding-experiment") << "  " << bb1.getName() << " total propagations # " << en1.d_numTotalPropagations << std::endl;
    Debug("encoding-experiment") << "  " << bb1.getName() << " shared propagations # " << en1.d_numSharedPropagations << std::endl;
										  
    Debug("encoding-experiment") << "  " << bb2.getName() << " unique propagate # " << en2_unique << std::endl;
    Debug("encoding-experiment") << "  " << bb2.getName() << " total propagations # " << en2.d_numTotalPropagations << std::endl;
    Debug("encoding-experiment") << "  " << bb2.getName() << " shared propagations # " << en2.d_numSharedPropagations << std::endl;
    
    
    if (en1_unique == 0 && en2_unique == 0)
      return EQUAL;

    if (en1_unique == 0 && en2_unique != 0)
      return LESS;

    if (en2_unique == 0 && en1_unique != 0)
      return GREATER;

    return INCOMPARABLE;
}


class Runner {
public:
  virtual void run(const std::vector<int>& assumps) = 0;
  virtual ~Runner() {} 
};


void sampleAssignments(unsigned num_fixed, unsigned num, Runner* runner, bool random_walk) {
  std::vector<unsigned> permutation;
  for (unsigned i = 0; i < num; ++i)
    permutation.push_back(i); 
  std::random_shuffle (permutation.begin(), permutation.end());

  unsigned num_iter = std::pow(2, num_fixed);

  for (unsigned iter = 0; iter < num_iter; ++iter) {
    Trace("encoding") << "RUNNING iteration " << iter << std::endl;
    std::vector<int> assumps;
    
    for (unsigned j = 0; j < num_fixed; ++j) {
      // if the jth bit of i is 1 negate the assumption
      if ((iter & (1 << j)) != 0) {
	//std::cout << "-" << permutation[j]<<" ";
	assumps.push_back(-permutation[j]);
      } else {
	//std::cout << permutation[j]<<" ";
	assumps.push_back(permutation[j]);
      }
    }

    if (random_walk) {
      // finish via random walk
      for (unsigned j = assumps.size(); j < permutation.size(); ++j) {
	bool negate = rand()%2;
	if (negate) {
	  assumps.push_back(-permutation[j]);
	} else {
	  assumps.push_back(permutation[j]);
	}
      }
    }

    runner->run(assumps); 
  }
}


struct ComparisonResult {
  std::string d_name1, d_name2;
  unsigned first_better;
  unsigned second_better;
  unsigned incomparable;
  unsigned equal;
  unsigned total;
  ComparisonResult(std::string name1, std::string name2)
    : d_name1(name1)
    , d_name2(name2)
    , first_better(0)
    , second_better(0)
    , incomparable(0)
    , equal(0)
    , total(0) {}

  void add(EncodingOrder order) {
    ++total;
    switch(order) {
    case EQUAL: ++equal; break;
    case LESS: ++second_better; break;
    case GREATER: ++first_better; break;
    case INCOMPARABLE: ++incomparable; break;
    default:
      Unreachable();
    }
  }
  friend  std::ostream& operator<<(std::ostream& os, const ComparisonResult& obj);
};

std::ostream& operator<<(std::ostream& os, const ComparisonResult& obj)
{
  os << obj.d_name1 << " better: " << obj.first_better << "("<<float(obj.first_better*100)/ obj.total <<"%)" <<std::endl;
  os << obj.d_name2 << " better: " << obj.second_better << "("<<float(obj.second_better*100)/ obj.total <<"%)" <<std::endl;
  os << "incomparable: " << obj.incomparable << "("<<float(obj.incomparable*100)/ obj.total <<"%)" <<std::endl;
  os << "equal: " << obj.equal << "("<<float(obj.equal*100)/ obj.total <<"%)" <<std::endl;
  os << "total: "<< obj.total << std::endl;
  return os;
}

class EncodingComparator : public Runner {
  Kind d_kind;
  context::Context* d_ctx;
  unsigned d_bitwidth;

  std::string d_name1;
  std::string d_name2;
  EncodingBitblaster d_encodingBB1;
  EncodingBitblaster d_encodingBB2;
  EncodingBitblaster::EncodingNotify* d_encodingNotify1;
  EncodingBitblaster::EncodingNotify* d_encodingNotify2;
 
  ComparisonResult d_cresult;
  Node d_assertion;
  vector<Node> d_all_bits1;
  vector<Node> d_all_bits2;
  bool d_keepLearned;
public:
  EncodingComparator(unsigned bitwidth, Kind k, bool keep_learned, 
		     TBitblaster<Node>::TermBBStrategy e1, std::string name1,
		     TBitblaster<Node>::TermBBStrategy e2, std::string name2)
    : d_kind(k)
    , d_ctx(new context::Context())
    , d_bitwidth(bitwidth)
    , d_name1(name1)
    , d_name2(name2)
    , d_encodingBB1(d_ctx, d_name1)
    , d_encodingBB2(d_ctx, d_name2)
    , d_encodingNotify1(NULL)
    , d_encodingNotify2(NULL)
    , d_cresult(name1, name2)
    , d_assertion()
    , d_all_bits1()
    , d_all_bits2()
    , d_keepLearned(keep_learned)
  {
    CnfStream* cnf1 = d_encodingBB1.getCnfStream();
    d_encodingBB1.setTermBBStrategy(k, e1);
    
    CnfStream* cnf2 = d_encodingBB2.getCnfStream();
    d_encodingBB2.setTermBBStrategy(k, e2);

    d_encodingNotify1 = new EncodingBitblaster::EncodingNotify(cnf2, &d_encodingBB1);
    d_encodingNotify2 = new EncodingBitblaster::EncodingNotify(cnf1, &d_encodingBB2);
    d_encodingBB1.setNotify(d_encodingNotify1);
    d_encodingBB2.setNotify(d_encodingNotify2);

    Node a = utils::mkVar(d_bitwidth);
    Node b = utils::mkVar(d_bitwidth);
    Node c = utils::mkVar(d_bitwidth);

    Node a_op_b = utils::mkNode(d_kind, a, b);
    d_assertion = utils::mkNode(kind::EQUAL, a_op_b, c);

    d_encodingBB1.assertFact(d_assertion);
    d_encodingBB2.assertFact(d_assertion);

    EncodingBitblaster::Bits a1_bits, b1_bits, c1_bits;
    d_encodingBB1.getBBTerm(a, a1_bits);
    d_encodingBB1.getBBTerm(b, b1_bits);
    d_encodingBB1.getBBTerm(c, c1_bits);

    EncodingBitblaster::Bits a2_bits, b2_bits, c2_bits;
    d_encodingBB2.getBBTerm(a, a2_bits);
    d_encodingBB2.getBBTerm(b, b2_bits);
    d_encodingBB2.getBBTerm(c, c2_bits);

    d_all_bits1.insert(d_all_bits1.begin(), a1_bits.begin(), a1_bits.end());
    d_all_bits1.insert(d_all_bits1.begin(), b1_bits.begin(), b1_bits.end());
    d_all_bits1.insert(d_all_bits1.begin(), c1_bits.begin(), c1_bits.end());

    d_all_bits2.insert(d_all_bits2.begin(), a2_bits.begin(), a2_bits.end());
    d_all_bits2.insert(d_all_bits2.begin(), b2_bits.begin(), b2_bits.end());
    d_all_bits2.insert(d_all_bits2.begin(), c2_bits.begin(), c2_bits.end());
  }

  virtual ~EncodingComparator() {
    delete d_encodingNotify1;
    delete d_encodingNotify2;
    delete d_ctx;
  }
  
  void run(const vector<int>& assump_index) {
    d_ctx->push();
    
    bool res1 = true;
    bool res2 = true;

    Debug("encoding") << "Fixed bits "<< std::endl;
    for (unsigned i = 0; i < assump_index.size(); ++i) {
      if (!d_keepLearned) {
	d_encodingBB1.clearLearnedClauses();
	d_encodingBB2.clearLearnedClauses();
      }

      TNode bit1, bit2;
      if(assump_index[i] < 0) {
	bit1 = utils::mkNot(d_all_bits1[-assump_index[i]]);
	bit2 = utils::mkNot(d_all_bits2[-assump_index[i]]);
      } else {
	bit1 = d_all_bits1[assump_index[i]];
	bit2 = d_all_bits2[assump_index[i]];
      }

      Debug("encoding") << bit1 << "/ "<<  bit2 <<" " <<std::endl;
      d_encodingBB1.assumeLiteral(bit1);
      res1 = d_encodingBB1.propagate();
      d_encodingBB2.assumeLiteral(bit2);
      res2 = d_encodingBB2.propagate();
      
      if (!res1 && res2)
	++d_cresult.first_better;
      if (!res2 && res1)
	++d_cresult.second_better;
      
      if (!res1 || ! res2)
	break;

      // check which one wins
      EncodingOrder order = comparePropagations(*d_encodingNotify1, *d_encodingNotify2,
						d_encodingBB1, d_encodingBB2);
      d_cresult.add(order);
    }


    // call solve to ensure that the encodings are correct
    res1 = res1 ? d_encodingBB1.solve() : res1;
    Debug("encoding") << "  " << d_encodingBB1.getName() <<" full solve result " << res1 << std::endl;
    Debug("encoding") << "   number of learned clauses " << d_encodingBB1.getNumLearnedClauses() << std::endl;
    res2 = res2 ? d_encodingBB2.solve() : res2;
    Debug("encoding") << "  " << d_encodingBB2.getName() <<" full solve result " << res2 << std::endl;
    Debug("encoding") << "   number of learned clauses " << d_encodingBB2.getNumLearnedClauses() << std::endl;
    
    Assert( res1 == res2);
    d_encodingNotify1->clear();
    d_encodingNotify2->clear();

    d_ctx->pop();
  }

  void printResults(std::ostream& os) {
    os << d_cresult;
  }
};


class EncodingContradiction : public Runner {
  Kind d_kind;
  context::Context* d_ctx;
  unsigned d_bitwidth;

  std::string d_name;
  EncodingBitblaster d_encodingBB;
  EncodingBitblaster d_oracleBB;
  //  EncodingBitblaster::EncodingNotify d_notify;
  std::vector<Node> d_allBits;
  unsigned d_missedContradictions;
public:
  EncodingContradiction(unsigned bitwidth, Kind k, 
		        TBitblaster<Node>::TermBBStrategy e, std::string name)
    : d_kind(k)
    , d_ctx(new context::Context())
    , d_bitwidth(bitwidth)
    , d_name(name)
    , d_encodingBB(d_ctx, d_name)
    , d_oracleBB(d_ctx, d_name+"oracle")
    // , d_notify(d_encodingBB.getCnfStream(), d_encodingBB1)
    // , d_notify_oracle(d_oracleBB.getCnfStream(), d_oracle)
    , d_allBits()
    , d_missedContradictions(0)
  {
    d_encodingBB.setTermBBStrategy(k, e);
    d_oracleBB.setTermBBStrategy(k, e);
    
    Node a = utils::mkVar(d_bitwidth);
    Node b = utils::mkVar(d_bitwidth);
    Node c = utils::mkVar(d_bitwidth);

    Node a_op_b = utils::mkNode(d_kind, a, b);
    Node assertion = utils::mkNode(kind::EQUAL, a_op_b, c);
    
    d_encodingBB.assertFact(assertion);
    d_oracleBB.assertFact(assertion);
    
    EncodingBitblaster::Bits a_bits, b_bits, c_bits;
    d_encodingBB.getBBTerm(a, a_bits);
    d_encodingBB.getBBTerm(b, b_bits);
    d_encodingBB.getBBTerm(c, c_bits);

    d_allBits.insert(d_allBits.begin(), a_bits.begin(), a_bits.end());
    d_allBits.insert(d_allBits.begin(), b_bits.begin(), b_bits.end());
    d_allBits.insert(d_allBits.begin(), c_bits.begin(), c_bits.end());
  }

  void run(const std::vector<int>& assump_index) {
    d_ctx->push();
    Debug("encoding") << "Push() " <<std::endl;
    
    bool res = true, res_oracle = true;
    
    for (unsigned i = 0; i < assump_index.size(); ++i) {
      d_encodingBB.clearLearnedClauses();

      TNode bit;
      if(assump_index[i] < 0) {
	bit = utils::mkNot(d_allBits[-assump_index[i]]);
      } else {
	bit = d_allBits[assump_index[i]];
      }

      Debug("encoding") << "Assuming bit " << bit <<std::endl;
      d_encodingBB.assumeLiteral(bit);
      d_oracleBB.assumeLiteral(bit);
      
      res = d_encodingBB.propagate();
      res_oracle = d_oracleBB.solve();
      
      if (!res_oracle && res) {
	++d_missedContradictions;
      }
      Assert (res || !res_oracle);
    }
    Debug("encoding") << "Pop() " <<std::endl;

    d_ctx->pop();
  }

  void print(ostream& os) {
    os << d_name << " missed contradictions " << d_missedContradictions << endl;
  }
};


void printTermEncoding(Kind k, TBitblaster<Node>::TermBBStrategy e, std::string name, unsigned bitwidth) {
  EncodingBitblaster eb(new context::Context(), name);
  eb.setTermBBStrategy(k, e);
  Node a = utils::mkVar(bitwidth);
  Node b = utils::mkVar(bitwidth);
  Node c = utils::mkVar(bitwidth);

  Node a_op_b = utils::mkNode(k, a, b);
  Node assertion = utils::mkNode(kind::EQUAL, a_op_b, c);
  
  eb.assertFact(assertion);

  eb.printCnfMapping();
  eb.printProblemClauses();
}

void printAtomEncoding(Kind k, TBitblaster<Node>::AtomBBStrategy e, std::string name, unsigned bitwidth) {
  EncodingBitblaster eb(new context::Context(), name);
  eb.setAtomBBStrategy(k, e);
  Node a = utils::mkVar(bitwidth);
  Node b = utils::mkVar(bitwidth);
  //NodeManager* nm = NodeManager::currentNM();
  //Node out = nm->mkSkolem("out", nm->booleanType());
  Node a_op_b = utils::mkNode(k, a, b);
  //Node assertion = utils::mkNode(kind::IFF, a_op_b, out);
  
  eb.bbAtom(a_op_b);

  eb.printCnfMapping();
  eb.printProblemClauses();
}


void CVC4::runEncodingExperiment(Options& opts) {
  ExprManager em;
  SmtEngine smt(&em);
  smt::SmtScope scope(&smt);
  std::cout << "Running encoding experiments " << std::endl; 

  unsigned num_fixed = opts[options::encodingNumFixed];
  unsigned width = opts[options::encodingBitwidth];

  printTermEncoding(kind::BITVECTOR_MULT, OptimalAddMultBB<Node>, "mult3", 3);
  printTermEncoding(kind::BITVECTOR_MULT, OptimalAddMultBB<Node>, "mult4", 4);

  printTermEncoding(kind::BITVECTOR_SHL, DefaultShlBB<Node>, "shl3", 3);
  printTermEncoding(kind::BITVECTOR_SHL, DefaultShlBB<Node>, "shl4", 4);

  printAtomEncoding(kind::BITVECTOR_ULT, DefaultUltBB<Node>, "ult3", 3);
  printAtomEncoding(kind::BITVECTOR_ULT, DefaultUltBB<Node>, "ult4", 4);

  
  
  // EncodingComparator ec_plus(width, kind::BITVECTOR_PLUS, false,
  // 			     DefaultPlusBB<Node>, "default-plus",
  // 			     OptimalPlusBB<Node>, "optimal-plus");

  // sampleAssignments(num_fixed, width*3, &ec_plus, true);
  // ec_plus.printResults(std::cout);

  // EncodingComparator ec_mult(width, kind::BITVECTOR_MULT, false,
  // 			     DefaultMultBB<Node>, "default-mult",
  // 			     OptimalAddMultBB<Node>, "optimal-add-mult");

  // sampleAssignments(num_fixed, width*3, &ec_mult, true);
  // ec_mult.printResults(std::cout);

  
  // EncodingContradiction ec_default(width, kind::BITVECTOR_PLUS, DefaultPlusBB<Node>, "default-plus");
  // EncodingContradiction ec_optimal(width, kind::BITVECTOR_PLUS, OptimalPlusBB<Node>, "optimal-plus");

  // sampleAssignments(num_fixed, width*3, &ec_default, true);
  // sampleAssignments(num_fixed, width*3, &ec_optimal, true);
  // ec_default.print(std::cout);
  // ec_optimal.print(std::cout);
}
