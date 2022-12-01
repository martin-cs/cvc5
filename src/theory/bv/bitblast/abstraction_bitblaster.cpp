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
 * Formula abstraction bit-blaster.
 */

#include "theory/bv/bitblast/abstraction_bitblaster.h"
#include "theory/bv/bitblast/bitblast_strategies_template.h"
#include "theory/bv/branch_hints.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
 
template <class T>
void AbstractionIteBB (TNode node, std::vector<T>& res, TBitblaster<T>* bb) {
  Assert(node.getKind() == kind::BITVECTOR_ITE);

  int p = hints::getBranchingHint(node[0]);
  int threshold = 0;

  std::vector<T> cond;
  Node assumption;
  NodeManager* nm = NodeManager::currentNM();
  
  if (p > threshold) {
    // Likely to happen
    Trace("abstraction-bb") << "Assuming " << node[0] << " is true" << std::endl;
    bb->bbTerm(node[1], res);
    assumption = nm->mkNode(kind::EQUAL, node[0], nm->mkConst(BitVector(1U, 1U)));

  } else if (p < -threshold) {
    // Unlikely to happen
    Trace("abstraction-bb") << "Assuming " << node[0] << " is false" << std::endl;
    bb->bbTerm(node[2], res);
    assumption = nm->mkNode(kind::EQUAL, node[0], nm->mkConst(BitVector(1U, 0U)));
    
  } else {
    DefaultIteBB<T>(node, res, bb);
    return;
  }

  // Add to assumptions
  bb->bbAtom(assumption);
  bb->registerAbstraction(assumption);

  return;
}

void AbstractionBitblaster::registerAbstraction(Node node) {
  abstractionAssumptions.push_back(node);
  return;
}

  
AbstractionBitblaster::AbstractionBitblaster(Env& env, TheoryState* s)
    : NodeBitblaster(env, s)
{
  // Hook the ITE bit-blast
  d_termBBStrategies[kind::BITVECTOR_ITE] = AbstractionIteBB<Node>;

  // Hook the non-linear terms
  //d_termBBStrategies[kind::BITVECTOR_UDIV] = DefaultUdivBB<T>;
  //d_termBBStrategies[kind::BITVECTOR_UREM] = DefaultUremBB<T>;
}

const std::vector<Node> & AbstractionBitblaster::getAbstractionAssumptions() const
{
  return abstractionAssumptions;
}


  
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
