/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <fstream>

#include <solvers/qbf/qbf_skizzo.h>
#include <solvers/qbf/qbf_quantor.h>

#include "compare_states.h"
#include "qbf_cache.h"

/*******************************************************************\

Function: compare_states

  Inputs:

 Outputs: return true iff state is subsumed

 Purpose:

\*******************************************************************/

qbf_cachet qbf_cache;

bool compare_states(
  formula_containert &formula_container,
  const statet &state,
  const statet &entry,
  const std::set<vart> &vars,
  bool use_cache)
{
  #ifdef DEBUG
  std::cout << "symbolic_simulatort::compare_states1\n";
  #endif
  
  const state_dt &state_d=state.data();
  
  // check "in_atomic_section"
  if(state_d.in_atomic_section!=entry.data().in_atomic_section)
    return false;
  
  // we do the conversion separately, as we need
  // different non-deterministic choices for both

  qbf_skizzot solver;
  //qbf_quantort solver;
  
  // first do the conversion for state

  // do the reset
  formula_container.reset_prop();
    
  typedef std::set<literalt> state_inputst;
  state_inputst state_inputs;

  literalt state_guard_literal=state_d.guard.convert(solver);
  state_d.guard.get_nondet_literals(state_inputs);

  // do the variables of the state
  bvt state_variables;
  state_variables.reserve(vars.size());
  
  for(std::set<vart>::const_iterator
      it=vars.begin();
      it!=vars.end();
      it++)
  {
    formulat f=state_d.get_var(it->var_nr, it->thread_nr);
    state_variables.push_back(f.convert(solver));
    f.get_nondet_literals(state_inputs);
  }

  literalt entry_guard_literal=
    entry.data().guard.convert(solver);

  bvt entry_variables;
  entry_variables.reserve(vars.size());

  for(std::set<vart>::const_iterator
      it=vars.begin();
      it!=vars.end();
      it++)
  {
    formulat f=entry.data().get_var(it->var_nr, it->thread_nr);
    entry_variables.push_back(f.convert(solver));
  }

  // FORALL x in state EXISTS y in entry
  // guard(x) => (guard(y) AND values(x)=values(y))
  
  // build values(x)=values(y)
  bvt eq_bv;
  eq_bv.reserve(vars.size()+1);
  
  for(unsigned i=0; i<entry_variables.size(); i++)
  {
    literalt l1=entry_variables[i];
    literalt l2=state_variables[i];
    eq_bv.push_back(solver.lequal(l1, l2));
  }
  
  eq_bv.push_back(entry_guard_literal);

  literalt conjunction=solver.land(eq_bv);

  bvt clause;
  clause.push_back(solver.lnot(state_guard_literal));
  clause.push_back(conjunction);
  solver.lcnf(clause);

  // build quantifiers
  // all the rest are existentially quantified implicitly

  for(state_inputst::const_iterator
      it=state_inputs.begin();
      it!=state_inputs.end();
      it++)
  {
    solver.add_quantifier(qdimacs_cnft::quantifiert::UNIVERSAL, *it);
  }
  
  if(use_cache)
  {
    switch(qbf_cache.check(solver))
    {
    case qbf_cachet::IS_TRUE:
      std::cout << "QBF instance is in cache: TRUE\n";
      return true;
    
    case qbf_cachet::IS_FALSE:
      std::cout << "QBF instance is in cache: FALSE\n";
      return false;
    
    default:;
    }
  }

  std::cout << "Running " << solver.solver_text() << ", "
            << solver.no_variables() << " variables, "
            << solver.no_clauses() << " clauses"
            << std::endl;
            
  bool result;

  switch(solver.prop_solve())
  {
  case propt::P_UNSATISFIABLE: // this is false
    result=false;
    break;
  
  case propt::P_SATISFIABLE: // this is true
    result=true;
    break;
    
  default:
    throw "Error from "+solver.solver_text();
  }
  
  if(use_cache)
    qbf_cache.set(solver, result);

  return result;
}
