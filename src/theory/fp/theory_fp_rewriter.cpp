/*********************                                                        */
/*! \file floatingpoint.cpp
 ** \verbatim
 ** Original author: Martin Brain
 ** Major contributors: 
 ** Minor contributors (to current version): 
 ** This file is *NOT* part of the CVC4 project.
 ** Copyright (c) 2013  University of Oxford
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Rewrite rules for floating point theories. ]]
 **
 ** \todo [[ Constant folding
 **          Push negations up through operators
 **          FLOATINGPOINT_FP to CONST_FLOATINGPOINT
 **          classifications to normal tests ]]
 **/

#include "theory/fp/theory_fp_rewriter.h"

#include "util/cvc4_assert.h"


namespace CVC4 {
namespace theory {
namespace fp {

namespace rewrite {
  /** Rewrite rules **/

  RewriteResponse notFP (TNode node, bool) {
    Unreachable("non floating-point kind (%d) in floating point rewrite?",node.getKind());
  }

  RewriteResponse identity (TNode node, bool) {
    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse type (TNode node, bool) {
    Unreachable("sort kind (%d) found in expression?",node.getKind());
    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse removeDoubleNegation (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_NEG);
    if (node[0].getKind() == kind::FLOATINGPOINT_NEG) {
      RewriteResponse(REWRITE_DONE, node[0][0]);
    }

    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse convertSubtractionToAddition (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_SUB);
    TNode negation = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_NEG,node[2]);
    TNode addition = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_PLUS,node[0],node[1],negation);
    return RewriteResponse(REWRITE_DONE, addition);
  }

  RewriteResponse geqToleq (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_GEQ);
    return RewriteResponse(REWRITE_DONE,NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_LEQ,node[1],node[0]));
  }

  RewriteResponse gtTolt (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_GT);
    return RewriteResponse(REWRITE_DONE,NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_LT,node[1],node[0]));
  }

  RewriteResponse removed (TNode node, bool) {  
    Unreachable("kind (%d) should have been removed?",node.getKind());
    return RewriteResponse(REWRITE_DONE, node);
  }

}; /* CVC4::theory::fp::rewrite */

RewriteFunction TheoryFpRewriter::preRewriteTable[kind::LAST_KIND]; 
RewriteFunction TheoryFpRewriter::postRewriteTable[kind::LAST_KIND]; 


  /**
   * Initialize the rewriter.
   */
  void TheoryFpRewriter::init() {

    /* Set up the pre-rewrite dispatch table */
    for (unsigned i = 0; i < kind::LAST_KIND; ++i) {
      preRewriteTable[i] = rewrite::notFP;
    }

    /******** Constants ********/
    /* No rewriting possible for constants */
    preRewriteTable[kind::CONST_FLOATINGPOINT] = rewrite::identity;
    preRewriteTable[kind::CONST_ROUNDINGMODE] = rewrite::identity; 

    /******** Sorts(?) ********/
    /* These kinds should only appear in types */
    //preRewriteTable[kind::ROUNDINGMODE_TYPE] = rewrite::type;
    preRewriteTable[kind::FLOATINGPOINT_TYPE] = rewrite::type;
      
    /******** Operations ********/
    preRewriteTable[kind::FLOATINGPOINT_FP] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_EQ] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_ABS] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_NEG] = rewrite::removeDoubleNegation;
    preRewriteTable[kind::FLOATINGPOINT_PLUS] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_SUB] = rewrite::convertSubtractionToAddition;
    preRewriteTable[kind::FLOATINGPOINT_MULT] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_DIV] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_FMA] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_SQRT] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_REM] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_RTI] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_MIN] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_MAX] = rewrite::identity;

    /******** Comparisons ********/
    preRewriteTable[kind::FLOATINGPOINT_LEQ] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_LT] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_GEQ] = rewrite::geqToleq;
    preRewriteTable[kind::FLOATINGPOINT_GT] = rewrite::gtTolt;

    /******** Classifications ********/
    preRewriteTable[kind::FLOATINGPOINT_ISN] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_ISSN] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_ISZ] = rewrite::identity;  
    preRewriteTable[kind::FLOATINGPOINT_ISINF] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_ISNAN] = rewrite::identity;

    /******** Conversions ********/
    preRewriteTable[kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_FP_REAL] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_UBV] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_SBV] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_REAL] = rewrite::identity;





    /* Set up the post-rewrite dispatch table */
    for (unsigned i = 0; i < kind::LAST_KIND; ++i) {
      postRewriteTable[i] = rewrite::notFP;
    }

    /******** Constants ********/
    /* No rewriting possible for constants */
    postRewriteTable[kind::CONST_FLOATINGPOINT] = rewrite::identity;
    postRewriteTable[kind::CONST_ROUNDINGMODE] = rewrite::identity; 

    /******** Sorts(?) ********/
    /* These kinds should only appear in types */
    //postRewriteTable[kind::ROUNDINGMODE_TYPE] = rewrite::type;
    postRewriteTable[kind::FLOATINGPOINT_TYPE] = rewrite::type;
      
    /******** Operations ********/
    postRewriteTable[kind::FLOATINGPOINT_FP] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_EQ] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_ABS] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_NEG] = rewrite::removeDoubleNegation;
    postRewriteTable[kind::FLOATINGPOINT_PLUS] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_SUB] = rewrite::removed;
    postRewriteTable[kind::FLOATINGPOINT_MULT] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_DIV] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_FMA] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_SQRT] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_REM] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_RTI] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_MIN] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_MAX] = rewrite::identity;

    /******** Comparisons ********/
    postRewriteTable[kind::FLOATINGPOINT_LEQ] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_LT] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_GEQ] = rewrite::removed;
    postRewriteTable[kind::FLOATINGPOINT_GT] = rewrite::removed;

    /******** Classifications ********/
    postRewriteTable[kind::FLOATINGPOINT_ISN] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_ISSN] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_ISZ] = rewrite::identity;  
    postRewriteTable[kind::FLOATINGPOINT_ISINF] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_ISNAN] = rewrite::identity;

    /******** Conversions ********/
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_REAL] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_UBV] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_SBV] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_REAL] = rewrite::identity;


  }




  /**
   * Rewrite a node into the normal form for the theory of fp
   * in pre-order (really topological order)---meaning that the
   * children may not be in the normal form.  This is an optimization
   * for theories with cancelling terms (e.g., 0 * (big-nasty-expression)
   * in arithmetic rewrites to 0 without the need to look at the big
   * nasty expression).  Since it's only an optimization, the
   * implementation here can do nothing.
   */

  RewriteResponse TheoryFpRewriter::preRewrite(TNode node) {
    RewriteResponse res = postRewriteTable [node.getKind()] (node, true);
    if (res.node != node) {
      Debug("floating-point-rewrite") << "TheoryFpRewriter::preRewrite before " << node << std::endl;
      Debug("floating-point-rewrite") << "TheoryFpRewriter::preRewrite after  " << res.node << std::endl;
    }
    return res;
  }


  /**
   * Rewrite a node into the normal form for the theory of fp.
   * Called in post-order (really reverse-topological order) when
   * traversing the expression DAG during rewriting.  This is the
   * main function of the rewriter, and because of the ordering,
   * it can assume its children are all rewritten already.
   *
   * This function can return one of three rewrite response codes
   * along with the rewritten node:
   *
   *   REWRITE_DONE indicates that no more rewriting is needed.
   *   REWRITE_AGAIN means that the top-level expression should be
   *     rewritten again, but that its children are in final form.
   *   REWRITE_AGAIN_FULL means that the entire returned expression
   *     should be rewritten again (top-down with preRewrite(), then
   *     bottom-up with postRewrite()).
   *
   * Even if this function returns REWRITE_DONE, if the returned
   * expression belongs to a different theory, it will be fully
   * rewritten by that theory's rewriter.
   */

  RewriteResponse TheoryFpRewriter::postRewrite(TNode node) {
    RewriteResponse res = postRewriteTable [node.getKind()] (node, false);
    if (res.node != node) {
      Debug("floating-point-rewrite") << "TheoryFpRewriter::postRewrite before " << node << std::endl;
      Debug("floating-point-rewrite") << "TheoryFpRewriter::postRewrite after  " << res.node << std::endl;
    }
    return res;
  }


}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

