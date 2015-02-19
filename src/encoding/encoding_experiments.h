/*********************                                                        */
/*! \file encoding_experiments.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Experimental setup for encoding paper
 **/

//#include "cvc4_private.h"

#ifndef __CVC4__ENCODING_EXPERIMENTS_H
#define __CVC4__ENCODING_EXPERIMENTS_H

#include <iostream>
#include <vector>

#include "expr/expr.h"
#include "util/cardinality.h"
#include "options/options.h"

namespace CVC4 {

void runEncodingExperiment(Options& opts);

}/* CVC4 namespace */

#endif  /* __CVC4__ENCODING_EXPERIMENTS_H */
