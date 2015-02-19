/*********************                                                        */
/*! \file bvminisat.cpp
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

#include "prop/eminisat/eminisat.h"
#include "prop/eminisat/simp/SimpSolver.h"

using namespace CVC4;
using namespace prop;

EMinisatSatSolver::EMinisatSatSolver(context::Context* mainSatContext, const std::string& name)
: context::ContextNotifyObj(mainSatContext, false),
  d_minisat(new EMinisat::SimpSolver(mainSatContext)),
  d_minisatNotify(0),
  d_assertionsCount(0),
  d_assertionsRealCount(mainSatContext, 0),
  d_lastPropagation(mainSatContext, 0),
  d_statistics(name)
{
  d_statistics.init(d_minisat); 
}


EMinisatSatSolver::~EMinisatSatSolver() throw(AssertionException) {
  delete d_minisat;
  delete d_minisatNotify;
}

void EMinisatSatSolver::setNotify(Notify* notify) {
  d_minisatNotify = new MinisatNotify(notify);
  d_minisat->setNotify(d_minisatNotify);
}

void EMinisatSatSolver::addClause(SatClause& clause, bool removable, uint64_t proof_id) {
  Debug("sat::minisat") << "Add clause " << clause <<"\n";
  EMinisat::vec<EMinisat::Lit> minisat_clause;
  toMinisatClause(clause, minisat_clause);
  // for(unsigned i = 0; i < minisat_clause.size(); ++i) {
  //   d_minisat->setFrozen(EMinisat::var(minisat_clause[i]), true);
  // }
  d_minisat->addClause(minisat_clause);
}

SatValue EMinisatSatSolver::propagate() {
  return toSatLiteralValue(d_minisat->propagateAssumptions());
}

void EMinisatSatSolver::addMarkerLiteral(SatLiteral lit) {
  d_minisat->addMarkerLiteral(EMinisat::var(toMinisatLit(lit)));
  markUnremovable(lit); 
}

void EMinisatSatSolver::explain(SatLiteral lit, std::vector<SatLiteral>& explanation) {
  std::vector<EMinisat::Lit> minisat_explanation;
  d_minisat->explain(toMinisatLit(lit), minisat_explanation);
  for (unsigned i = 0; i < minisat_explanation.size(); ++i) {
    explanation.push_back(toSatLiteral(minisat_explanation[i])); 
  }
}

SatValue EMinisatSatSolver::assertAssumption(SatLiteral lit, bool propagate) {
  d_assertionsCount ++;
  d_assertionsRealCount = d_assertionsRealCount + 1;
  return toSatLiteralValue(d_minisat->assertAssumption(toMinisatLit(lit), propagate));
}

void EMinisatSatSolver::contextNotifyPop() {
  while (d_assertionsCount > d_assertionsRealCount) {
    popAssumption();
    d_assertionsCount --;
  }
}

void EMinisatSatSolver::popAssumption() {
  d_minisat->popAssumption();
}

SatVariable EMinisatSatSolver::newVar(bool isTheoryAtom, bool preRegister, bool canErase){
  return d_minisat->newVar(true, true, !canErase);
}

void EMinisatSatSolver::markUnremovable(SatLiteral lit){
  d_minisat->setFrozen(EMinisat::var(toMinisatLit(lit)), true);
}


void EMinisatSatSolver::interrupt(){
  d_minisat->interrupt();
}

SatValue EMinisatSatSolver::solve(){
  ++d_statistics.d_statCallsToSolve;
  return toSatLiteralValue(d_minisat->solve());
}

SatValue EMinisatSatSolver::solve(long unsigned int& resource){
  Trace("limit") << "MinisatSatSolver::solve(): have limit of " << resource << " conflicts" << std::endl;
  ++d_statistics.d_statCallsToSolve;
  if(resource == 0) {
    d_minisat->budgetOff();
  } else {
    d_minisat->setConfBudget(resource);
  }
  //  EMinisat::vec<EMinisat::Lit> empty;
  unsigned long conflictsBefore = d_minisat->conflicts;
  SatValue result = toSatLiteralValue(d_minisat->solveLimited());
  d_minisat->clearInterrupt();
  resource = d_minisat->conflicts - conflictsBefore;
  Trace("limit") << "<MinisatSatSolver::solve(): it took " << resource << " conflicts" << std::endl;
  return result;
}

void EMinisatSatSolver::getUnsatCore(SatClause& unsatCore) {
  // TODO add assertion to check the call was after an unsat call
  for (int i = 0; i < d_minisat->conflict.size(); ++i) {
    unsatCore.push_back(toSatLiteral(d_minisat->conflict[i]));
  }
}

SatValue EMinisatSatSolver::value(SatLiteral l){
	return toSatLiteralValue(d_minisat->value(toMinisatLit(l)));
}

SatValue EMinisatSatSolver::modelValue(SatLiteral l){
	return toSatLiteralValue(d_minisat->modelValue(toMinisatLit(l)));
}

void EMinisatSatSolver::unregisterVar(SatLiteral lit) {
  // this should only be called when user context is implemented
  // in the BVSatSolver
  Unreachable();
}

void EMinisatSatSolver::renewVar(SatLiteral lit, int level) {
  // this should only be called when user context is implemented
  // in the BVSatSolver

  Unreachable();
}

unsigned EMinisatSatSolver::getAssertionLevel() const {
  // we have no user context implemented so far
  return 0;
}

// converting from internal Minisat representation

SatVariable EMinisatSatSolver::toSatVariable(EMinisat::Var var) {
  if (var == var_Undef) {
    return undefSatVariable;
  }
  return SatVariable(var);
}

EMinisat::Lit EMinisatSatSolver::toMinisatLit(SatLiteral lit) {
  if (lit == undefSatLiteral) {
    return EMinisat::lit_Undef;
  }
  return EMinisat::mkLit(lit.getSatVariable(), lit.isNegated());
}

SatLiteral EMinisatSatSolver::toSatLiteral(EMinisat::Lit lit) {
  if (lit == EMinisat::lit_Undef) {
    return undefSatLiteral;
  }

  return SatLiteral(SatVariable(EMinisat::var(lit)),
                    EMinisat::sign(lit));
}

SatValue EMinisatSatSolver::toSatLiteralValue(EMinisat::lbool res) {
  if(res == (EMinisat::lbool((uint8_t)0))) return SAT_VALUE_TRUE;
  if(res == (EMinisat::lbool((uint8_t)2))) return SAT_VALUE_UNKNOWN;
  Assert(res == (EMinisat::lbool((uint8_t)1)));
  return SAT_VALUE_FALSE;
}

void EMinisatSatSolver::toMinisatClause(SatClause& clause,
                                           EMinisat::vec<EMinisat::Lit>& minisat_clause) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    minisat_clause.push(toMinisatLit(clause[i]));
  }
  Assert(clause.size() == (unsigned)minisat_clause.size());
}

void EMinisatSatSolver::toSatClause(EMinisat::vec<EMinisat::Lit>& clause,
                                       SatClause& sat_clause) {
  for (int i = 0; i < clause.size(); ++i) {
    sat_clause.push_back(toSatLiteral(clause[i]));
  }
  Assert((unsigned)clause.size() == sat_clause.size());
}

void EMinisatSatSolver::clearLearned() {
  d_minisat->clearLearned();
}
int EMinisatSatSolver::getNumLearned() {
  return d_minisat->getNumLearned();
}
void EMinisatSatSolver::getLearnedClause(unsigned i, SatClause& clause) {
  EMinisat::vec<EMinisat::Lit> mclause;
  d_minisat->getLearnedClause(i, mclause);
  toSatClause(mclause, clause);
}

int EMinisatSatSolver::getNumClauses() {
  return d_minisat->getNumClauses();
}
void EMinisatSatSolver::getProblemClause(unsigned i, SatClause& clause) {
  EMinisat::vec<EMinisat::Lit> mclause;
  d_minisat->getProblemClause(i, mclause);
  toSatClause(mclause, clause);
}


// Satistics for EMinisatSatSolver

EMinisatSatSolver::Statistics::Statistics(const std::string& prefix) :
  d_statStarts("theory::bv::"+prefix+"bvminisat::starts"),
  d_statDecisions("theory::bv::"+prefix+"bvminisat::decisions"),
  d_statRndDecisions("theory::bv::"+prefix+"bvminisat::rnd_decisions"),
  d_statPropagations("theory::bv::"+prefix+"bvminisat::propagations"),
  d_statConflicts("theory::bv::"+prefix+"bvminisat::conflicts"),
  d_statClausesLiterals("theory::bv::"+prefix+"bvminisat::clauses_literals"),
  d_statLearntsLiterals("theory::bv::"+prefix+"bvminisat::learnts_literals"),
  d_statMaxLiterals("theory::bv::"+prefix+"bvminisat::max_literals"),
  d_statTotLiterals("theory::bv::"+prefix+"bvminisat::tot_literals"),
  d_statEliminatedVars("theory::bv::"+prefix+"bvminisat::eliminated_vars"),
  d_statCallsToSolve("theory::bv::"+prefix+"bvminisat::calls_to_solve", 0),
  d_statSolveTime("theory::bv::"+prefix+"bvminisat::solve_time", 0),
  d_registerStats(!prefix.empty())
{
  if (!d_registerStats)
    return;

  StatisticsRegistry::registerStat(&d_statStarts);
  StatisticsRegistry::registerStat(&d_statDecisions);
  StatisticsRegistry::registerStat(&d_statRndDecisions);
  StatisticsRegistry::registerStat(&d_statPropagations);
  StatisticsRegistry::registerStat(&d_statConflicts);
  StatisticsRegistry::registerStat(&d_statClausesLiterals);
  StatisticsRegistry::registerStat(&d_statLearntsLiterals);
  StatisticsRegistry::registerStat(&d_statMaxLiterals);
  StatisticsRegistry::registerStat(&d_statTotLiterals);
  StatisticsRegistry::registerStat(&d_statEliminatedVars);
  StatisticsRegistry::registerStat(&d_statCallsToSolve);
  StatisticsRegistry::registerStat(&d_statSolveTime);
}

EMinisatSatSolver::Statistics::~Statistics() {
  if (!d_registerStats)
    return;
  StatisticsRegistry::unregisterStat(&d_statStarts);
  StatisticsRegistry::unregisterStat(&d_statDecisions);
  StatisticsRegistry::unregisterStat(&d_statRndDecisions);
  StatisticsRegistry::unregisterStat(&d_statPropagations);
  StatisticsRegistry::unregisterStat(&d_statConflicts);
  StatisticsRegistry::unregisterStat(&d_statClausesLiterals);
  StatisticsRegistry::unregisterStat(&d_statLearntsLiterals);
  StatisticsRegistry::unregisterStat(&d_statMaxLiterals);
  StatisticsRegistry::unregisterStat(&d_statTotLiterals);
  StatisticsRegistry::unregisterStat(&d_statEliminatedVars);
  StatisticsRegistry::unregisterStat(&d_statCallsToSolve);
  StatisticsRegistry::unregisterStat(&d_statSolveTime);
}

void EMinisatSatSolver::Statistics::init(EMinisat::SimpSolver* minisat){
  if (!d_registerStats)
    return;
  
  d_statStarts.setData(minisat->starts);
  d_statDecisions.setData(minisat->decisions);
  d_statRndDecisions.setData(minisat->rnd_decisions);
  d_statPropagations.setData(minisat->propagations);
  d_statConflicts.setData(minisat->conflicts);
  d_statClausesLiterals.setData(minisat->clauses_literals);
  d_statLearntsLiterals.setData(minisat->learnts_literals);
  d_statMaxLiterals.setData(minisat->max_literals);
  d_statTotLiterals.setData(minisat->tot_literals);
  d_statEliminatedVars.setData(minisat->eliminated_vars);
}
