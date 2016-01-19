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

std::pair<Node, std::pair <Node, Node> >
CVC4::theory::bv::optimalMaxGadget(const Node a, const Node b,
                                   const Node a_max, const Node b_max,
                                   CVC4::prop::CnfStream* cnf) {
 
  Debug("encoding-generated") << "optimalMaxGadget" <<std::endl;

  NodeManager* nm = NodeManager::currentNM();
  Node a_max_out = nm->mkSkolem("a_max", nm->booleanType());
  Node b_max_out = nm->mkSkolem("b_max", nm->booleanType());
  Node max = nm->mkSkolem("max", nm->booleanType());

  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b_max), b_max_out), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a_max), a_max_out), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a_max_out), utils::mkNot(b_max_out)), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a), max, utils::mkNot(b)), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a), b_max_out, max), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b), utils::mkNot(a_max_out), a_max), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b, utils::mkNot(max), a_max_out), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b, a, utils::mkNot(max)), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b_max_out, a, utils::mkNot(max)), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a_max_out), a, a_max), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, max, utils::mkNot(b_max_out), b_max), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a), utils::mkNot(b_max_out), b_max), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, max, a_max, utils::mkNot(b)), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a_max_out), max, a_max), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b, utils::mkNot(b_max_out), b_max), 
                        false, false, RULE_INVALID, TNode::null());

  return std::make_pair(max, std::make_pair(a_max_out, b_max_out));
}

std::pair<Node, std::pair<Node, Node> >
CVC4::theory::bv::optimalSMaxGadget(const Node a,
                                    const Node b,
                                    CVC4::prop::CnfStream* cnf) {
  Debug("encoding-generated") << "optimalSMaxGadget" <<std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Node a_max_out = nm->mkSkolem("a_max", nm->booleanType());
  Node b_max_out = nm->mkSkolem("b_max", nm->booleanType());
  Node max = nm->mkSkolem("max", nm->booleanType());
  

  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a_max_out), utils::mkNot(a)), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b_max_out), utils::mkNot(b)), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b_max_out), a), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(max), a), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a_max_out), b), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(max), b), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a), max, b_max_out), 
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a_max_out, utils::mkNot(b), max), 
                        false, false, RULE_INVALID, TNode::null());
  return std::make_pair(max, std::make_pair(a_max_out, b_max_out));
}

void CVC4::theory::bv::optimalSMax(const std::vector<Node>& a_bits,
                                  const std::vector<Node>& b_bits,
                                  std::vector<Node>& bits,
                                  CVC4::prop::CnfStream* cnf) {
  unsigned size = a_bits.size();
  Assert (bits.size() == 0 &&
          a_bits.size() == b_bits.size());
  
   std::pair<Node, std::pair<Node, Node> > res = optimalSMaxGadget(a_bits[size-1],
                                                                   b_bits[size-1],
                                                                   cnf);

  bits.resize(size);
  bits[size-1] = res.first;
  
  if (size == 1) {
    return;
  }
  Node a_max = res.second.first;
  Node b_max = res.second.second;
  
  for (int i = size - 2; i >=0; --i) {
    Node a = a_bits[i];
    Node b = b_bits[i];
    res = optimalMaxGadget(a, b, a_max, b_max, cnf);
    Node max = res.first;
    bits[i] = max;
    // update max values
    a_max = res.second.first;
    b_max = res.second.second;
  }
}

std::pair<Node, std::pair <Node, Node> >
CVC4::theory::bv::optimalMinGadget(const Node a, const Node b,
                                   const Node a_min, const Node b_min,
                                   CVC4::prop::CnfStream* cnf) {
 
  Debug("encoding-generated") << "optimalMinGadget" <<std::endl;

  NodeManager* nm = NodeManager::currentNM();
  Node a_min_out = nm->mkSkolem("a_min", nm->booleanType());
  Node b_min_out = nm->mkSkolem("b_min", nm->booleanType());
  Node min = nm->mkSkolem("min", nm->booleanType());

  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b_min), b_min_out),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a_min_out, utils::mkNot(a_min)),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b_min_out), utils::mkNot(a_min_out)),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b), min, utils::mkNot(a)),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, min, utils::mkNot(a), b_min_out),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, min, utils::mkNot(b), a_min_out),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b_min, utils::mkNot(b_min_out), utils::mkNot(min)),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b_min, utils::mkNot(b), utils::mkNot(b_min_out)),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b_min, utils::mkNot(min), a),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a_min, utils::mkNot(min), b),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a_min, utils::mkNot(a_min_out), utils::mkNot(min)),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a_min, utils::mkNot(a_min_out), b),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b_min, utils::mkNot(b_min_out), a),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a_min, utils::mkNot(a), utils::mkNot(a_min_out)),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(min), b, a),
                        false, false, RULE_INVALID, TNode::null());

  return std::make_pair(min, std::make_pair(a_min_out, b_min_out));
}

std::pair<Node, std::pair<Node, Node> >
CVC4::theory::bv::optimalSMinGadget(const Node a,
                                    const Node b,
                                    CVC4::prop::CnfStream* cnf) {
  Debug("encoding-generated") << "optimalSMinGadget" <<std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Node a_min_out = nm->mkSkolem("a_min", nm->booleanType());
  Node b_min_out = nm->mkSkolem("b_min", nm->booleanType());
  Node min = nm->mkSkolem("min", nm->booleanType());

  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b_min_out), utils::mkNot(a)),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, min, utils::mkNot(a)),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(a_min_out), utils::mkNot(b)),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, min, utils::mkNot(b)),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, utils::mkNot(b_min_out), b),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a, utils::mkNot(a_min_out)),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, a, utils::mkNot(min), b_min_out),
                        false, false, RULE_INVALID, TNode::null());
  cnf->convertAndAssert(nm->mkNode(kind::OR, b, a_min_out, utils::mkNot(min)),
                        false, false, RULE_INVALID, TNode::null());

  return std::make_pair(min, std::make_pair(a_min_out, b_min_out));
}

void CVC4::theory::bv::optimalSMin(const std::vector<Node>& a_bits,
                                  const std::vector<Node>& b_bits,
                                  std::vector<Node>& bits,
                                  CVC4::prop::CnfStream* cnf) {
  unsigned size = a_bits.size();
  Assert (bits.size() == 0 &&
          a_bits.size() == b_bits.size());
  
   std::pair<Node, std::pair<Node, Node> > res = optimalSMinGadget(a_bits[size-1],
                                                                   b_bits[size-1],
                                                                   cnf);

  bits.resize(size);
  bits[size-1] = res.first;
  
  if (size == 1) {
    return;
  }
  Node a_min = res.second.first;
  Node b_min = res.second.second;
  
  for (int i = size - 2; i >=0; --i) {
    Node a = a_bits[i];
    Node b = b_bits[i];
    res = optimalMinGadget(a, b, a_min, b_min, cnf);
    Node min = res.first;
    bits[i] = min;
    // update min values
    a_min = res.second.first;
    b_min = res.second.second;
  }
}
