/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simulator_base.h"

/*******************************************************************\

Function: simulator_baset::make_initial_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

statet simulator_baset::make_initial_state()
{
  statet state;

  // initially, we have one thread
  state.data_w().threads.clear();
  
  state.data_w().threads.push_back(statet::threadt());
  statet::threadt &thread=state.data_w().threads.back();
  
  thread.program=&(program_formula.function_map["main"].body);
  thread.PC=thread.start_pc();

  // initialize global variables with false

  state.data_w().globals.resize(
    program_formula.no_globals,
    formula_container.gen_false());

  // here it gets to be non-deterministic
  // a different one for each variable!
  
  for(unsigned v=0; v<state.data().globals.size(); v++)
    state.data_w().globals[v]=formula_container.gen_nondet();

  // initialize locals the same way
  
  thread.locals.resize(
    program_formula.no_locals,
    formula_container.gen_false());

  for(unsigned v=0; v<thread.locals.size(); v++)
    thread.locals[v]=formula_container.gen_nondet();

  // initialize guard with true
  state.data_w().guard=formula_container.gen_true();

  // mark it as initial state
  state.data_w().is_initial_state=true;
  
  return state;
}

/*******************************************************************\

Function: simulator_baset::instantiate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

formulat simulator_baset::instantiate(
  const state_dt &current,
  const state_dt *next,
  unsigned t,
  formulat formula)
{
  if(formula.is_null()) return formula;

  switch(formula.id())
  {
  case formula_nodet::CONST_TRUE:
  case formula_nodet::CONST_FALSE:
    return formula;

  case formula_nodet::VARIABLE:
    return current.get_var(formula.variable(), t);

  case formula_nodet::NEXT_VARIABLE:
    assert(next!=NULL);
    return next->get_var(formula.variable(), t);
    
  case formula_nodet::NOT:
    return formula_container.gen_not(
      instantiate(current, next, t, formula.a()));

  case formula_nodet::AND:
    return formula_container.gen_and(
      instantiate(current, next, t, formula.a()),
      instantiate(current, next, t, formula.b()));

  case formula_nodet::OR:
    return formula_container.gen_or(
      instantiate(current, next, t, formula.a()),
      instantiate(current, next, t, formula.b()));

  case formula_nodet::NONDET:
  case formula_nodet::IFF:
  case formula_nodet::XOR:
    return formula_container.new_node(
      formula.id(),
      instantiate(current, next, t, formula.a()),
      instantiate(current, next, t, formula.b()));

  default:
    assert(false);
  }
  
  assert(false);
  return formulat(NULL);
}

