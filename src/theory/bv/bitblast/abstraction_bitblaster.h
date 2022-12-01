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
 * A Bitblaster that handles formula abstractions
 */
#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BITBLAST_ABSTRACTION_BITBLASTER_H
#define CVC5__THEORY__BV__BITBLAST_ABSTRACTION_BITBLASTER_H

#include "theory/bv/bitblast/node_bitblaster.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

/**
 * Adds an implementation of formula abstraction.
 *
 */

class AbstractionBitblaster : public NodeBitblaster
{
  
 public:
  AbstractionBitblaster(Env& env, TheoryState* state);
  ~AbstractionBitblaster() = default;

  const std::vector<Node> & getAbstractionAssumptions() const;

  virtual void registerAbstraction(Node node) override;

 private:
  std::vector<Node> abstractionAssumptions;
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif
