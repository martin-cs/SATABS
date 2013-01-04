/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <solvers/sat/satcheck.h>

#include "simulator.h"

/*******************************************************************\

Function: simulator_baset::compute_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_baset::compute_trace(
  const statet &error_state,
  tracet &trace,
  bool assertion)
{
  std::cout << "Computing trace" << std::endl;;

  // first collect the states
  trace.clear();
    
  for(const statet *s=&error_state;
      !s->is_null();
      s=&(s->data().previous))
  {
    const statet &state=*s;
    trace.push_front(trace_stept());
    trace_stept &trace_step=trace.front();
    trace_step.copy_from(state);
  }

  trace.back().is_error_state=true;
  
  // now do the reset
  formula_container.reset_prop();

  // now solve
  
  satcheckt satcheck;

  for(tracet::iterator it=trace.begin();
      it!=trace.end();
      it++)
  {
    const state_dt &d=it->state.data();

    #ifdef DEBUG
    std::cout << "GUARD: " << d.guard << std::endl;

    if(!trace_step.is_initial_state)
      program_formula.threads[trace_step.previous_thread].formula_goto_program.
        output_instruction(std::cout, trace_step.previous_PC);
    #endif
    
    // add guard as constraint
    satcheck.l_set_to(d.guard.convert(satcheck), true);
    
    // convert variables
    it->convert(satcheck);
  }

  if(assertion)
  {
    const instructiont &last_instruction=*error_state.data().previous_PC;

    assert(last_instruction.is_assert());
  
    formulat instantiated_guard=
      instantiate(
        error_state,
        error_state.data().previous_thread,
        last_instruction.guard);

    #ifdef DEBUG
    std::cout << "ASSERTION: ";
    instantiated_guard.output(std::cout, program_formula.variables);
    std::cout << std::endl;
    #endif

    satcheck.l_set_to(instantiated_guard.convert(satcheck), false);    
  }
  
  // run SAT

  std::cout << "Running " << satcheck.solver_text() << ", "
            << satcheck.no_variables() << " variables, "
            << satcheck.no_clauses() << " clauses" << std::endl;
  
  switch(satcheck.prop_solve())
  {
  case propt::P_SATISFIABLE: // this is what we expect
    break;
    
  case propt::P_UNSATISFIABLE:
    assert(false);
    
  default:
    assert(false);
  }

  // gather values from satisfying assignment
  
  for(tracet::iterator t_it=trace.begin();
      t_it!=trace.end();
      t_it++)
    t_it->get_values(satcheck);
}
