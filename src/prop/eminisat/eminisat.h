/*********************                                                        */
/*! \file bvminisat.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors:
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2014  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** Implementation of the minisat for cvc4 (bitvectors).
 **/

#include "cvc4_private.h"

#pragma once

#include "prop/sat_solver.h"
#include "prop/eminisat/simp/SimpSolver.h"
#include "context/cdo.h"

namespace CVC4 {
namespace prop {

class EMinisatSatSolver : public EncodingSatSolverInterface, public context::ContextNotifyObj {

private:

  class MinisatNotify : public EMinisat::Notify {
    EncodingSatSolverInterface::Notify* d_notify;
  public:
    MinisatNotify(EncodingSatSolverInterface::Notify* notify)
    : d_notify(notify)
    {}
    bool notify(EMinisat::Lit lit) {
      return d_notify->notify(toSatLiteral(lit));
    }
    void notify(EMinisat::vec<EMinisat::Lit>& clause) {
      SatClause satClause;
      toSatClause(clause, satClause);
      d_notify->notify(satClause);
    }

  };

  EMinisat::SimpSolver* d_minisat;
  MinisatNotify* d_minisatNotify;

  unsigned d_assertionsCount;
  context::CDO<unsigned> d_assertionsRealCount;
  context::CDO<unsigned> d_lastPropagation;

protected:

  void contextNotifyPop();

public:

  EMinisatSatSolver() :
    ContextNotifyObj(NULL, false),
    d_assertionsRealCount(NULL, (unsigned)0),
    d_lastPropagation(NULL, (unsigned)0),
    d_statistics("")
  { Unreachable(); }
  EMinisatSatSolver(context::Context* mainSatContext, const std::string& name = "");
  ~EMinisatSatSolver() throw(AssertionException);

  void setNotify(Notify* notify);

  void addClause(SatClause& clause, bool removable, uint64_t proof_id);

  SatValue propagate();

  SatVariable newVar(bool isTheoryAtom = false, bool preRegister = false, bool canErase = true);

  SatVariable trueVar() { return d_minisat->trueVar(); }
  SatVariable falseVar() { return d_minisat->falseVar(); }

  void markUnremovable(SatLiteral lit);

  void interrupt();
  
  SatValue solve();
  SatValue solve(long unsigned int&);
  void getUnsatCore(SatClause& unsatCore);

  SatValue value(SatLiteral l);
  SatValue modelValue(SatLiteral l);

  void unregisterVar(SatLiteral lit);
  void renewVar(SatLiteral lit, int level = -1);
  unsigned getAssertionLevel() const;


  // helper methods for converting from the internal Minisat representation

  static SatVariable     toSatVariable(EMinisat::Var var);
  static EMinisat::Lit    toMinisatLit(SatLiteral lit);
  static SatLiteral      toSatLiteral(EMinisat::Lit lit);
  static SatValue toSatLiteralValue(EMinisat::lbool res);

  static void  toMinisatClause(SatClause& clause, EMinisat::vec<EMinisat::Lit>& minisat_clause);
  static void  toSatClause    (EMinisat::vec<EMinisat::Lit>& clause, SatClause& sat_clause);
  void addMarkerLiteral(SatLiteral lit);

  void explain(SatLiteral lit, std::vector<SatLiteral>& explanation);

  SatValue assertAssumption(SatLiteral lit, bool propagate);
  
  void popAssumption();

  void clearLearned();
  int getNumLearned();
  void getLearnedClause(unsigned i, SatClause& clause);

  int getNumClauses();
  void getProblemClause(unsigned i, SatClause& clause);

  
  class Statistics {
  public:
    ReferenceStat<uint64_t> d_statStarts, d_statDecisions;
    ReferenceStat<uint64_t> d_statRndDecisions, d_statPropagations;
    ReferenceStat<uint64_t> d_statConflicts, d_statClausesLiterals;
    ReferenceStat<uint64_t> d_statLearntsLiterals,  d_statMaxLiterals;
    ReferenceStat<uint64_t> d_statTotLiterals;
    ReferenceStat<int> d_statEliminatedVars;
    IntStat d_statCallsToSolve;
    BackedStat<double> d_statSolveTime;
    bool d_registerStats;
    Statistics(const std::string& prefix);
    ~Statistics();
    void init(EMinisat::SimpSolver* minisat);
  };

  Statistics d_statistics;
};

}
}




