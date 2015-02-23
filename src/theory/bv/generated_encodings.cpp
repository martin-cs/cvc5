/*********************                                                        */
/*! \file generated_encodings.cpp
** \verbatim
** Original author: Liana Hadarean
** This file is part of the CVC4 project.
** Copyright (c) 2009-2014  New York University and The University of Iowa
** See the file COPYING in the top-level source directory for licensing
** information.\endverbatim
**
** \brief Automatically generated optimally propagating encodings.
**
** Automatically generated optimally propagating encodings.
**/

#include "cvc4_private.h"
#include "theory/bv/generated_encodings.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv; 

std::pair<Node, Node> CVC4::theory::bv::optimalFullAdder(const Node a, const Node b,
								const Node cin,
								CVC4::prop::CnfStream* cnf) {

  NodeManager* nm = NodeManager::currentNM();
  Node s = nm->mkSkolem("sum", nm->booleanType());
  Node cout = nm->mkSkolem("carry", nm->booleanType());
  
  Node na = nm->mkNode(kind::NOT, a);
  Node nb = nm->mkNode(kind::NOT, b);
  Node ncin = nm->mkNode(kind::NOT, cin);
  Node ncout = nm->mkNode(kind::NOT, cout);
  Node ns = nm->mkNode(kind::NOT, s);

  cnf->convertAndAssert(nm->mkNode(kind::OR, na, nb, cout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, na, ncin, cout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, nb, ncin, cout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, na, s, cout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, nb, s, cout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, ncin, s, cout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, na, nb, ncin, s),
			false, false, RULE_INVALID, TNode::null());

  cnf->convertAndAssert(nm->mkNode(kind::OR, a, b, ncout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a, cin, ncout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b, cin, ncout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a, ns, ncout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b, ns, ncout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, cin, ns, ncout),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a,b, cin,ns),
			false, false, RULE_INVALID, TNode::null());
  return std::make_pair(s, cout);
}
 
template <>
std::pair<Node, Node> CVC4::theory::bv::optimalUltGadget(const Node &answerFound, const Node &answer,
								const Node &a, const Node &b,
								CVC4::prop::CnfStream* cnf) {
  NodeManager* nm = NodeManager::currentNM();
  Node answerFoundOut = nm->mkSkolem("answerFoundOut", nm->booleanType());
  Node answerOut = nm->mkSkolem("answerOut", nm->booleanType());
  std::vector<Node> clause;

  cnf->convertAndAssert(nm->mkNode(kind::OR, answerFoundOut, utils::mkNot(answerFound)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, answerFoundOut, b, utils::mkNot(a)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, answer, utils::mkNot(answerOut), utils::mkNot(a)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, answerFoundOut, answerOut, utils::mkNot(answer)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(answer), answerOut, a),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, answer, b, utils::mkNot(answerOut)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, answerFoundOut, answer, utils::mkNot(answerOut)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, answerFoundOut, utils::mkNot(b), a),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(answerFound), answer, utils::mkNot(answerOut)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, answerOut, utils::mkNot(answer), utils::mkNot(b)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(answerFound), answerOut, utils::mkNot(answer)),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b);
  clause.push_back(utils::mkNot(answerFoundOut));
  clause.push_back(utils::mkNot(answerOut));
  clause.push_back(answerFound);
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a);
  clause.push_back(b);
  clause.push_back(answerFound);
  clause.push_back(utils::mkNot(answerFoundOut));
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b));
  clause.push_back(answerOut);
  clause.push_back(answerFound);
  clause.push_back(utils::mkNot(answerFoundOut));
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b));
  clause.push_back(utils::mkNot(answerFoundOut));
  clause.push_back(utils::mkNot(a));
  clause.push_back(answerFound);
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(answerOut);
  clause.push_back(answerFound);
  clause.push_back(a);
  clause.push_back(utils::mkNot(answerFoundOut));
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(answerFoundOut));
  clause.push_back(utils::mkNot(answerOut));
  clause.push_back(utils::mkNot(a));
  clause.push_back(answerFound);
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());

  return std::make_pair(answerFoundOut, answerOut);
}

template<>
Node CVC4::theory::bv::optimalSignGadget(const Node& a,
					 const Node& b,
					 const Node &aLTb,
					 CVC4::prop::CnfStream* cnf) {
  NodeManager* nm = NodeManager::currentNM();
  Node aSLTb = nm->mkSkolem("aSLTb", nm->booleanType());

  cnf->convertAndAssert(nm->mkNode(kind::OR, b, aSLTb, utils::mkNot(a)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b, aSLTb, utils::mkNot(aLTb)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a, utils::mkNot(aSLTb), aLTb),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a, utils::mkNot(aSLTb), utils::mkNot(b)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, aLTb, utils::mkNot(aSLTb), utils::mkNot(b)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(aLTb), aSLTb, utils::mkNot(a)),
			false, false, RULE_INVALID, TNode::null());

  return aSLTb;
}

template<>
void CVC4::theory::bv::optimalMult2(const std::vector<Node>&a,
					   const std::vector<Node>& b,
					   std::vector<Node>& c, prop::CnfStream* cnf) {
  
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult2()" <<std::endl;
  unsigned bitwidth = 2;
  Assert(a.size() == b.size() && a.size() == bitwidth &&
	 c.size() == 0);

  for (unsigned i = 0; i < 2*bitwidth; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }
  
  std::vector<Node> clause;
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[3]), c[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[1]), utils::mkNot(c[3])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(c[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[2]), utils::mkNot(c[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(c[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[2]), a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[3]), a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[2]), b[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[3]), b[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[2]), utils::mkNot(a[0]), c[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], a[0], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[2]), utils::mkNot(b[0]), c[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, c[0], utils::mkNot(b[0]), utils::mkNot(a[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], a[1], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], b[1], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], a[0], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(c[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(c[1]); 
  clause.push_back(c[3]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(a[0])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(c[1]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
}
template<>
void CVC4::theory::bv::optimalMult3(const std::vector<Node>&a,
					   const std::vector<Node>& b,
					   std::vector<Node>& c, CVC4::prop::CnfStream* cnf) {
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult3()" <<std::endl;
  unsigned bitwidth = 3;
  Assert(a.size() == b.size() && a.size() == bitwidth &&
	 c.size() == 0);

  for (unsigned i = 0; i < 2*bitwidth; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }

  std::vector<Node> clause;
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[0]), b[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), b[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[0]), a[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), a[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), a[2], b[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[4]), b[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), b[1], b[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[3]), b[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], utils::mkNot(c[3]), b[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), b[1], utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], a[1], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], b[1], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), c[1], b[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), b[1], c[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[0]), utils::mkNot(c[3])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(b[0]), utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), utils::mkNot(c[0]), utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), a[1], b[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), a[2], b[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), utils::mkNot(c[3]), b[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), b[0], b[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, c[0], utils::mkNot(b[0]), utils::mkNot(a[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), c[1], utils::mkNot(c[3])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[4]), a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[4]), utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[4]), utils::mkNot(c[3])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), c[1], a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), utils::mkNot(c[3]), a[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), a[2], a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[3]), utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[2], utils::mkNot(c[3]), a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[3]), a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[4]), c[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(a[0]), utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), c[0], a[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), utils::mkNot(c[2]), utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[5]), a[1], utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], a[1], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], a[0], utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(c[4]), a[0], a[2]),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(c[2]); 
  clause.push_back(c[1]); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(c[1]); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[0])); 
  clause.push_back(c[1]); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(a[1]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(c[2]); 
  clause.push_back(c[1]); 
  clause.push_back(c[4]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(c[1]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(c[4]); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(c[1]); 
  clause.push_back(c[4]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(c[1]); 
  clause.push_back(b[1]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(b[1]); 
  clause.push_back(c[3]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(b[1]); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(a[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[3]); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(b[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(a[0])); 
  clause.push_back(b[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(utils::mkNot(c[0])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(c[0]); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(b[0])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(a[1]); 
  clause.push_back(c[4]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(c[2]); 
  clause.push_back(c[3]); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(c[0]); 
  clause.push_back(utils::mkNot(c[1])); 
  clause.push_back(c[3]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(c[0]); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(a[0])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(c[1])); 
  clause.push_back(utils::mkNot(b[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[5])); 
  clause.push_back(utils::mkNot(a[0])); 
  clause.push_back(c[1]); 
  clause.push_back(c[4]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[0])); 
  clause.push_back(c[1]); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(c[4]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[0]); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(utils::mkNot(c[1])); 
  clause.push_back(c[3]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(utils::mkNot(c[0])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[2]); 
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(c[4])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(a[1]); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(a[0])); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(a[1]); 
  clause.push_back(c[4]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(utils::mkNot(a[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[0]); 
  clause.push_back(a[2]); 
  clause.push_back(c[1]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[1]); 
  clause.push_back(a[2]); 
  clause.push_back(c[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(a[2]); 
  clause.push_back(c[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[2]); 
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(b[0])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(utils::mkNot(a[0])); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[0]); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[1]); 
  clause.push_back(b[2]); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[1]); 
  clause.push_back(b[2]); 
  clause.push_back(c[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[0]); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(c[1])); 
  clause.push_back(utils::mkNot(a[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(b[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[0]); 
  clause.push_back(a[0]); 
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[0]); 
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[2]); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[3]); 
  clause.push_back(a[1]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(b[2]); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[2]); 
  clause.push_back(a[1]); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[2]); 
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[0]); 
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(a[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[0]); 
  clause.push_back(b[1]); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[1]); 
  clause.push_back(a[2]); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[0]); 
  clause.push_back(a[1]); 
  clause.push_back(b[2]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[0]); 
  clause.push_back(a[2]); 
  clause.push_back(b[1]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(b[0]); 
  clause.push_back(a[0]); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(a[1]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[0]); 
  clause.push_back(a[2]); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(c[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(c[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(c[5]); 
  clause.push_back(c[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[5]); 
  clause.push_back(c[2]); 
  clause.push_back(c[3]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[2]); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(c[1])); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[0])); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(utils::mkNot(c[0])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(a[0]); 
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[3]); 
  clause.push_back(c[5]); 
  clause.push_back(utils::mkNot(a[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[3]); 
  clause.push_back(c[4]); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(utils::mkNot(c[1])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(utils::mkNot(a[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(c[1])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(c[2])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(c[0]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[2]); 
  clause.push_back(c[4]); 
  clause.push_back(c[5]); 
  clause.push_back(utils::mkNot(a[0])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(utils::mkNot(b[1])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(a[1]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(utils::mkNot(b[1])); 
  clause.push_back(utils::mkNot(a[2])); 
  clause.push_back(c[5]); 
  clause.push_back(utils::mkNot(b[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(c[2]); 
  clause.push_back(utils::mkNot(c[3])); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(c[4]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(utils::mkNot(c[4])); 
  clause.push_back(a[1]); 
  clause.push_back(c[3]); 
  clause.push_back(c[2]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(c[0]); 
  clause.push_back(c[2]); 
  clause.push_back(a[1]); 
  clause.push_back(utils::mkNot(b[0])); 
  clause.push_back(utils::mkNot(a[2])); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(a[1])); 
  clause.push_back(b[1]); 
  clause.push_back(c[3]); 
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(c[5]); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(b[2])); 
  clause.push_back(b[1]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(c[3]); 
clause.push_back(c[5]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(c[2]); 
clause.push_back(c[5]); 
clause.push_back(c[3]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(b[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[3]); 
clause.push_back(a[1]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[5]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[2]); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[3]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(c[5]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[3]); 
clause.push_back(a[1]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[5]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[0]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(utils::mkNot(b[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[0]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(c[3]); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[5]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(c[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[0]); 
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[2]); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[3]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[2]); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(b[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[1]); 
clause.push_back(c[0]); 
clause.push_back(c[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(utils::mkNot(c[3])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(c[1]); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[2]); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(a[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[0]); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[0]); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(a[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[5]); 
clause.push_back(utils::mkNot(c[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[2]); 
clause.push_back(a[1]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(b[1]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[0]); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[5]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[2]); 
clause.push_back(c[3]); 
clause.push_back(c[5]); 
clause.push_back(utils::mkNot(c[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(c[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[2]); 
clause.push_back(a[1]); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(a[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(b[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[5]); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(c[2]); 
clause.push_back(c[5]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(a[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[3])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[5]); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[1]); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[1]); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[0]); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[3]); 
clause.push_back(c[4]); 
clause.push_back(c[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[1]); 
clause.push_back(c[0]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(c[3]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[0]); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[1]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(a[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(c[3]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(c[2]); 
clause.push_back(c[5]); 
clause.push_back(utils::mkNot(a[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[4])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(c[4])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(c[4])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[0])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[4]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(a[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[1]); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(c[4])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[0]); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(c[1]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[0]); 
clause.push_back(utils::mkNot(c[3])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[0]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[1]); 
clause.push_back(c[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[0]); 
clause.push_back(c[3]); 
clause.push_back(a[1]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(b[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(utils::mkNot(c[3])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(c[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[0]); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(a[1]); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[0]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(c[2]); 
clause.push_back(b[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[3]); 
clause.push_back(a[1]); 
clause.push_back(utils::mkNot(c[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[2]); 
clause.push_back(c[1]); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(a[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(a[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(b[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[0]); 
clause.push_back(b[1]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(c[4]); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[0]); 
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(c[1]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[0]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(utils::mkNot(c[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[0]); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(a[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[0]); 
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(a[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(b[0]); 
clause.push_back(b[2]); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(b[1]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[0]); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(b[1])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(b[2]); 
clause.push_back(c[2]); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(b[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(c[2])); 
clause.push_back(utils::mkNot(a[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(a[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[0]); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(c[3]); 
clause.push_back(utils::mkNot(b[2])); 
clause.push_back(c[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(c[1]); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(a[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[2])); 
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(b[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(c[2]); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(b[2]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(c[4])); 
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(a[0]); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(utils::mkNot(a[0])); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(b[1])); 
clause.push_back(c[2]); 
clause.push_back(c[0]); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[2]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(utils::mkNot(b[0])); 
clause.push_back(c[1]); 
clause.push_back(utils::mkNot(b[2])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(utils::mkNot(a[1])); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(c[1])); 
clause.push_back(utils::mkNot(b[0])); 
cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
false, false, RULE_INVALID, TNode::null());
clause.clear();
clause.push_back(a[0]); 
clause.push_back(utils::mkNot(c[3])); 
clause.push_back(b[2]); 
clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[2]); 
 clause.push_back(a[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[2]); 
 clause.push_back(c[1]); 
 clause.push_back(b[2]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(c[5])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(b[2]); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(b[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[2]); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[5]); 
 clause.push_back(c[0]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[2]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[1]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[2]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[4]); 
 clause.push_back(c[1]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[1]); 
 clause.push_back(c[5]); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[3]); 
 clause.push_back(a[1]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[4]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[3]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(b[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[5]); 
 clause.push_back(c[2]); 
 clause.push_back(c[0]); 
 clause.push_back(c[4]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[4]); 
 clause.push_back(c[0]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[2]); 
 clause.push_back(c[1]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[3]); 
 clause.push_back(c[5]); 
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[4])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(c[4])); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[2]); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[4])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[4])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[2]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[3]); 
 clause.push_back(c[5]); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(c[1]); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(c[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(a[1]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(b[1]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(c[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[2]); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[3]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[2]); 
 clause.push_back(c[5]); 
 clause.push_back(c[4]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[4]); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(a[2]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(b[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[5]); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[2]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[3]); 
 clause.push_back(c[0]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[5]); 
 clause.push_back(c[4]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[5]); 
 clause.push_back(c[4]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[5]); 
 clause.push_back(c[3]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[4]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[4]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[2]); 
 clause.push_back(a[1]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[0]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[1]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(c[2]); 
 clause.push_back(c[3]); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(b[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[3]); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[3]); 
 clause.push_back(b[1]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(b[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[3]); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[5]); 
 clause.push_back(c[4]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[1]); 
 clause.push_back(c[2]); 
 clause.push_back(b[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(a[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[5]); 
 clause.push_back(c[3]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[2]); 
 clause.push_back(a[1]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[1]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(a[1]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(b[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(c[5]); 
 clause.push_back(a[0]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[5]); 
 clause.push_back(c[2]); 
 clause.push_back(a[0]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(b[1]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(a[2]); 
 clause.push_back(utils::mkNot(c[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[5]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(b[1]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[3]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(b[2]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(b[2]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(c[1]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[3]); 
 clause.push_back(a[2]); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(a[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(a[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 clause.push_back(b[0]); 
 clause.push_back(c[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(c[2]); 
 clause.push_back(a[2]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(b[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(c[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[4]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(a[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(c[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[1]); 
 clause.push_back(c[2]); 
 clause.push_back(a[1]); 
 clause.push_back(utils::mkNot(a[0])); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(c[3]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(c[2]); 
 clause.push_back(a[2]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[5]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(a[1]); 
 clause.push_back(b[2]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[4]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(c[4])); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(b[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[1])); 
 clause.push_back(c[5]); 
 clause.push_back(utils::mkNot(c[3])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(c[2]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(a[2])); 
 clause.push_back(c[5]); 
 clause.push_back(c[0]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[0]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(b[1]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(c[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(b[1]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(a[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(c[4])); 
 clause.push_back(utils::mkNot(a[1])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(a[0]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(utils::mkNot(b[2])); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(a[1]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(utils::mkNot(b[0])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(b[1]); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(c[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(c[4]); 
 clause.push_back(a[1]); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[0]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(a[1]); 
 clause.push_back(c[1]); 
 clause.push_back(utils::mkNot(c[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(a[0]); 
 clause.push_back(utils::mkNot(c[3])); 
 clause.push_back(b[1]); 
 clause.push_back(c[4]); 
 clause.push_back(utils::mkNot(c[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(b[1]); 
 clause.push_back(a[2]); 
 clause.push_back(utils::mkNot(c[1])); 
 clause.push_back(c[3]); 
 clause.push_back(utils::mkNot(c[2])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
 clause.clear();
 clause.push_back(c[3]); 
 clause.push_back(a[1]); 
 clause.push_back(b[2]); 
 clause.push_back(utils::mkNot(c[2])); 
 clause.push_back(utils::mkNot(c[1])); 
 cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
		       false, false, RULE_INVALID, TNode::null());
}

template<>
void CVC4::theory::bv::optimalMult4(const std::vector<Node>&a,
					   const std::vector<Node>& b,
					   std::vector<Node>& c, CVC4::prop::CnfStream* cnf) {
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult4()" <<std::endl;
  unsigned bitwidth = 4;
  Assert(a.size() == b.size() && a.size() == bitwidth &&
	 c.size() == 0);

  for (unsigned i = 0; i < 2*bitwidth; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }

}

template<>
inline void CVC4::theory::bv::optimalMult2Aux(const std::vector<Node>&a,
					      const std::vector<Node>& b,
					      std::vector<Node>& c, CVC4::prop::CnfStream* cnf) {
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult2Aux()" <<std::endl;
  unsigned bitwidth = 2;
  Assert(a.size() == b.size() && a.size() == bitwidth &&
	 c.size() == 0);

  for (unsigned i = 0; i < 2*bitwidth; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }

}


template<>
inline void CVC4::theory::bv::optimalMult3Aux(const std::vector<Node>&a,
					      const std::vector<Node>& b,
					      std::vector<Node>& c, CVC4::prop::CnfStream* cnf) {
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult3Aux()" <<std::endl;
  unsigned bitwidth = 3;
  Assert(a.size() == b.size() && a.size() == bitwidth &&
	 c.size() == 0);

  for (unsigned i = 0; i < 2*bitwidth; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }

}

template<>
inline void CVC4::theory::bv::optimalMult4Aux(const std::vector<Node>&a,
					   const std::vector<Node>& b,
					   std::vector<Node>& c, CVC4::prop::CnfStream* cnf) {
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult4Aux()" <<std::endl;
  unsigned bitwidth = 4;
  Assert(a.size() == b.size() && a.size() == bitwidth &&
	 c.size() == 0);

  for (unsigned i = 0; i < 2*bitwidth; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }

}

inline void CVC4::theory::bv::optimalMult2Debug(const std::vector<Node>&a,
						const std::vector<Node>& b,
						std::vector<Node>& c, CVC4::prop::CnfStream* cnf) {
  unsigned size = 2;
  Assert(a.size() == b.size() && a.size() == size);
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult2Debug" <<std::endl;

  Assert(a.size() == b.size() && a.size() == size &&
	 c.size() == 0);
  for (unsigned i = 0; i < size; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }
  Node x1 = nm->mkSkolem("x", nm->booleanType());
  Node x2 = nm->mkSkolem("x", nm->booleanType());
  Node x3 = nm->mkSkolem("x", nm->booleanType());
  Node x4 = nm->mkSkolem("x", nm->booleanType());
  Node x5 = nm->mkSkolem("x", nm->booleanType());

  std::vector<Node> clause;
  
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[1]), x1),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], utils::mkNot(x2)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x2)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[1]), utils::mkNot(a[0]), x2),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x1), utils::mkNot(x2), x3),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x1), x3, x4),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x2), x3, x4),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, x2, utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x2, utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x3), utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x2, utils::mkNot(x3), utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x3), utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, x2, utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x5)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x5)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[0]), x5),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x5), c[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x5, utils::mkNot(c[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x4), c[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x4, utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());

  
}

inline void CVC4::theory::bv::optimalMult3Debug(const std::vector<Node>&a,
						const std::vector<Node>& b,
						std::vector<Node>& c, CVC4::prop::CnfStream* cnf) {
  unsigned size = 3;
  Assert(a.size() == b.size() && a.size() == size);
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult3Debug" <<std::endl;

  Assert(a.size() == b.size() && a.size() == size &&
	 c.size() == 0);
  
  for (unsigned i = 0; i < size; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }

  std::vector<Node> clause;
  Node x1 = nm->mkSkolem("x", nm->booleanType());
  Node x2 = nm->mkSkolem("x", nm->booleanType());
  Node x3 = nm->mkSkolem("x", nm->booleanType());
  Node x4 = nm->mkSkolem("x", nm->booleanType());
  Node x5 = nm->mkSkolem("x", nm->booleanType());
  Node x6 = nm->mkSkolem("x", nm->booleanType());
  Node x7 = nm->mkSkolem("x", nm->booleanType());
  Node x8 = nm->mkSkolem("x", nm->booleanType());
  Node x9 = nm->mkSkolem("x", nm->booleanType());
  Node x10 = nm->mkSkolem("x", nm->booleanType());
  Node x11 = nm->mkSkolem("x", nm->booleanType());
  Node x12 = nm->mkSkolem("x", nm->booleanType());

  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[1]), x1),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], utils::mkNot(x2)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x2)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[1]), utils::mkNot(a[0]), x2),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x1), utils::mkNot(x2), x3),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x1), x3, x4),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x2), x3, x4),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, x2, utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x2, utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x3), utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x2, utils::mkNot(x3), utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x3), utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, x2, utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x5)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[2], utils::mkNot(x5)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[2]), x5),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], utils::mkNot(x6)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], utils::mkNot(x6)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[1]), utils::mkNot(b[1]), x6),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x5), utils::mkNot(x6), x7),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x3), utils::mkNot(x5), x7),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x3), utils::mkNot(x6), x7),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x5), x7, x8),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x6), x7, x8),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x3), x7, x8),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(x3)); 
  clause.push_back(utils::mkNot(x5)); 
  clause.push_back(utils::mkNot(x6)); 
  clause.push_back(x8); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x5, x6, utils::mkNot(x7)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x3, x5, utils::mkNot(x7)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x3, x6, utils::mkNot(x7)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x5, utils::mkNot(x7), utils::mkNot(x8)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x6, utils::mkNot(x7), utils::mkNot(x8)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x3, utils::mkNot(x7), utils::mkNot(x8)),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(x3); 
  clause.push_back(x5); 
  clause.push_back(x6); 
  clause.push_back(utils::mkNot(x8)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[2], utils::mkNot(x9)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x9)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[0]), utils::mkNot(b[2]), x9),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x8), utils::mkNot(x9), x10),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x8), x10, x11),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x9), x10, x11),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x8, x9, utils::mkNot(x10)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x8, utils::mkNot(x10)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x9, utils::mkNot(x10)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x8, utils::mkNot(x10), utils::mkNot(x11)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x9, utils::mkNot(x10), utils::mkNot(x11)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x10), utils::mkNot(x11)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x8, x9, utils::mkNot(x11)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x12)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x12)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[0]), x12),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x12), c[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x12, utils::mkNot(c[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x4), c[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x4, utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x11), c[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x11, utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());

} 

inline void CVC4::theory::bv::optimalMult4Debug(const std::vector<Node>&a,
			      const std::vector<Node>& b,
			      std::vector<Node>& c, prop::CnfStream* cnf) {
  unsigned size = 4;
  Assert(a.size() == b.size() && a.size() == size);
  NodeManager* nm = NodeManager::currentNM();
  Debug("encoding-generated") << "   optimalMult2Debug" <<std::endl;

  Assert(a.size() == b.size() && a.size() == size &&
	 c.size() == 0);
  
  for (unsigned i = 0; i < size; ++i) {
    c.push_back(nm->mkSkolem("c", nm->booleanType()));
  }

  std::vector<Node> clause;
  Node x1 = nm->mkSkolem("x", nm->booleanType());
  Node x2 = nm->mkSkolem("x", nm->booleanType());
  Node x3 = nm->mkSkolem("x", nm->booleanType());
  Node x4 = nm->mkSkolem("x", nm->booleanType());
  Node x5 = nm->mkSkolem("x", nm->booleanType());
  Node x6 = nm->mkSkolem("x", nm->booleanType());
  Node x7 = nm->mkSkolem("x", nm->booleanType());
  Node x8 = nm->mkSkolem("x", nm->booleanType());
  Node x9 = nm->mkSkolem("x", nm->booleanType());
  Node x10 = nm->mkSkolem("x", nm->booleanType());
  Node x11 = nm->mkSkolem("x", nm->booleanType());
  Node x12 = nm->mkSkolem("x", nm->booleanType());
  Node x13 = nm->mkSkolem("x", nm->booleanType());
  Node x14 = nm->mkSkolem("x", nm->booleanType());
  Node x15 = nm->mkSkolem("x", nm->booleanType());
  Node x16 = nm->mkSkolem("x", nm->booleanType());
  Node x17 = nm->mkSkolem("x", nm->booleanType());
  Node x18 = nm->mkSkolem("x", nm->booleanType());
  Node x19 = nm->mkSkolem("x", nm->booleanType());
  Node x20 = nm->mkSkolem("x", nm->booleanType());
  Node x21 = nm->mkSkolem("x", nm->booleanType());

  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[1]), x1),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x1)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[1]), utils::mkNot(a[0]), x1),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x1), utils::mkNot(x1), x2),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x1), x2, x3),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x1), x2, x3),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, x1, utils::mkNot(x2)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x2)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x2)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x2), utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, utils::mkNot(x2), utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x2), utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x1, x1, utils::mkNot(x3)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[2], utils::mkNot(x4)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[2]), x4),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], utils::mkNot(x5)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], utils::mkNot(x5)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[1]), utils::mkNot(b[1]), x5),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x4), utils::mkNot(x5), x6),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x2), utils::mkNot(x4), x6),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x2), utils::mkNot(x5), x6),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x4), x6, x7),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x5), x6, x7),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x2), x6, x7),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(x2)); 
  clause.push_back(utils::mkNot(x4)); 
  clause.push_back(utils::mkNot(x5)); 
  clause.push_back(x7); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x4, x5, utils::mkNot(x6)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x2, x4, utils::mkNot(x6)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x2, x5, utils::mkNot(x6)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x4, utils::mkNot(x6), utils::mkNot(x7)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x5, utils::mkNot(x6), utils::mkNot(x7)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x2, utils::mkNot(x6), utils::mkNot(x7)),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(x2); 
  clause.push_back(x4); 
  clause.push_back(x5); 
  clause.push_back(utils::mkNot(x7)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x8)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[3], utils::mkNot(x8)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[3]), x8),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[1], utils::mkNot(x9)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[2], utils::mkNot(x9)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[1]), utils::mkNot(a[2]), x9),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x8), utils::mkNot(x9), x10),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x6), utils::mkNot(x8), x10),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x6), utils::mkNot(x9), x10),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x8), x10, x21),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x9), x10, x21),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x6), x10, x21),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(x6)); 
  clause.push_back(utils::mkNot(x8)); 
  clause.push_back(utils::mkNot(x9)); 
  clause.push_back(x21); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x8, x9, utils::mkNot(x10)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x6, x8, utils::mkNot(x10)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x6, x9, utils::mkNot(x10)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x8, utils::mkNot(x10), utils::mkNot(x21)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x9, utils::mkNot(x10), utils::mkNot(x21)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x6, utils::mkNot(x10), utils::mkNot(x21)),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(x6); 
  clause.push_back(x8); 
  clause.push_back(x9); 
  clause.push_back(utils::mkNot(x21)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[2], utils::mkNot(x11)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x11)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[0]), utils::mkNot(b[2]), x11),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x7), utils::mkNot(x11), x12),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x7), x12, x13),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x11), x12, x13),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x7, x11, utils::mkNot(x12)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x7, utils::mkNot(x12)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x11, utils::mkNot(x12)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x7, utils::mkNot(x12), utils::mkNot(x13)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x11, utils::mkNot(x12), utils::mkNot(x13)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x12), utils::mkNot(x13)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x7, x11, utils::mkNot(x13)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[2], utils::mkNot(x14)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[1], utils::mkNot(x14)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[1]), utils::mkNot(b[2]), x14),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x21), utils::mkNot(x14), x15),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x21), utils::mkNot(x12), x15),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x12), utils::mkNot(x14), x15),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x21), x15, x16),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x14), x15, x16),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x12), x15, x16),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(utils::mkNot(x21)); 
  clause.push_back(utils::mkNot(x12)); 
  clause.push_back(utils::mkNot(x14)); 
  clause.push_back(x16); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x21, x14, utils::mkNot(x15)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x21, x12, utils::mkNot(x15)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x12, x14, utils::mkNot(x15)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x21, utils::mkNot(x15), utils::mkNot(x16)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x14, utils::mkNot(x15), utils::mkNot(x16)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x12, utils::mkNot(x15), utils::mkNot(x16)),
			false, false, RULE_INVALID, TNode::null());
  clause.clear();
  clause.push_back(x21); 
  clause.push_back(x12); 
  clause.push_back(x14); 
  clause.push_back(utils::mkNot(x16)); 
  cnf->convertAndAssert(nm->mkNode(kind::OR, clause),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[3], utils::mkNot(x17)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x17)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a[0]), utils::mkNot(b[3]), x17),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x16), utils::mkNot(x17), x18),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x16), x18, x19),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x17), x18, x19),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x16, x17, utils::mkNot(x18)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x16, utils::mkNot(x18)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x17, utils::mkNot(x18)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x16, utils::mkNot(x18), utils::mkNot(x19)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x17, utils::mkNot(x18), utils::mkNot(x19)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x18), utils::mkNot(x19)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x16, x17, utils::mkNot(x19)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b[0], utils::mkNot(x20)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a[0], utils::mkNot(x20)),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b[0]), utils::mkNot(a[0]), x20),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x20), c[0]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x20, utils::mkNot(c[0])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x3), c[1]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x3, utils::mkNot(c[1])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x13), c[2]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x13, utils::mkNot(c[2])),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(x19), c[3]),
			false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, x19, utils::mkNot(c[3])),
			false, false, RULE_INVALID, TNode::null());
} 
