/******************************************************************************
 * Top contributors (to current version):
 *   Martin Brain
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Branching hints for BITVECTOR_ITE.
 */

#include "theory/bv/branch_hints.h"

#include "expr/attribute.h"


//using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace hints {

// Branching scores are stored using attributes
struct BranchingHintAttributeId {};
using BranchingHintAttribute = expr::Attribute<BranchingHintAttributeId, uint64_t>;
  
void setBranchingHint(Node node, int p)
{
  Trace("theory-bv-branchingHint") << "TheoryBV::setBranchingHint(): " << node << " set to " << p << std::endl;

  if (p != 0) {
    Assert(-100 <= p && p <= 100);

    int q = p;
    Node working = node;
    while (working.getKind() == kind::BITVECTOR_NOT) {
      working = working[0];
      q = -q;
    }
    BranchingHintAttribute attr;
    working.setAttribute(attr, q);
  }
  
  return;
}

int getBranchingHint(Node node)
{
  BranchingHintAttribute attr;

  // Normalising out the negations is actually needed
  int multiplier = 1;
  Node working = node;
  while (working.getKind() == kind::BITVECTOR_NOT) {
    working = working[0];
    multiplier *= -1;
  }
  
  if (working.hasAttribute(attr)) {
    int p = working.getAttribute(attr) * multiplier;

    Trace("theory-bv-branchingHint") << "TheoryBV::getBranchingHint(): " << node << " ~~> " << p << std::endl;
    Assert(-100 <= p && p <= 100 && p != 0);

    return p;
  } else {
    Trace("theory-bv-branchingHint") << "TheoryBV::getBranchingHint(): " << node << " not found" << std::endl;
    return 0;
  }

  Unreachable();
}

bool hasBranchingHint(Node node)
{
  BranchingHintAttribute attr;

  // Normalising out the negations is actually needed
  Node working = node;
  while (working.getKind() == kind::BITVECTOR_NOT) {
    working = working[0];
  }
  
  return working.hasAttribute(attr);
}

}  // namespace hints
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
