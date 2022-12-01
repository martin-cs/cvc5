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

#include "cvc5_private.h"

#pragma once

#include "expr/attribute.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace hints {

  // Sets the branching hint, 100 for very likely, 0 for neutral, -100 for very unlikely
  void setBranchingHint(Node node, int p);

  // Will return 0 if no hint has been registered
  // Will return -getBranchingHint(negation(node)) if the negation is registered
  int getBranchingHint(Node node);

  // True if there is a hint
  bool hasBranchingHint(Node node);
}
}
}
}  // namespace cvc5::internal
