/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <time_stopping.h>

#include "simulator_ct.h"

/*******************************************************************\

Function: simulator_ctt::compute_successor_states

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_ctt::compute_successor_states(
  const statet &state,
  edget &edge)
{
  assert(!state.data().threads.front().is_at_end());

  const program_formulat::formula_goto_programt::instructiont
    &instruction=*state.data().threads.front().PC;

  if(instruction.is_goto())
    compute_goto_successors(state, edge.queue);
  else if(instruction.is_end_thread())
    return; // just drop
  else if(instruction.is_return())
    execute_return(state, edge);
  else if(instruction.is_function_call())
    execute_functioncall(state, edge);
  else
  {
    statet new_state=state;
    new_state.set_previous(state, 0);

    execute_instruction(new_state, instruction);

    // get next PC: just increment
    new_state.data_w().threads.front().PC++;
    edge.queue.add(new_state);
  }
}

/*******************************************************************\

Function: simulator_ctt::explore

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_ctt::explore(
  const statet &state,
  edget &edge)
{
  // dump it if the guard is false
  if(state.data().guard.is_false())
    return;
    
  state_counter++;

  // at end of function?
  if(state.data().threads.front().is_at_end())
  {
    execute_return(state, edge);
    return;
  }
  
  const program_formulat::formula_goto_programt::instructiont
    &instruction=*state.data().threads.front().PC;
    
  if(instruction.code.can_form_cycle)
    if(has_recurrence(state))
      return; // just drop

  compute_successor_states(state, edge);
}

/*******************************************************************\

Function: simulator_ctt::simulator

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_ctt::simulator()
{
  std::cout << "Starting Symbolic Simulation"
            << std::endl;

  error_state_found=false;
  path_counter=1;
  state_counter=0;

  fine_timet start_time=current_time();
  
  summarize();

  if(error_state_found)
    std::cout << "VERIFICATION FAILED" << std::endl;
  else
    std::cout << "VERIFICATION SUCCESSFUL" << std::endl;

  std::cout << std::endl;
  std::cout << "Runtime: ";
  output_time(current_time()-start_time, std::cout);
  std::cout << std::endl;
  std::cout << "Paths: " << path_counter << std::endl;
  std::cout << "States explored: " << state_counter << std::endl;
}

/*******************************************************************\

Function: simulator_ctt::make_exit_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

statet simulator_ctt::make_exit_state(const irep_idt &function)
{
  statet state;

  // initially, we have one thread
  state.data_w().threads.clear();
  
  state.data_w().threads.push_back(statet::threadt());
  statet::threadt &thread=state.data_w().threads.back();
  
  const program_formulat::functiont &f=
    program_formula.function_map[function];
  
  thread.program=&(f.body);
  thread.PC=thread.program->instructions.end();

  // initialize global variables with false

  state.data_w().globals.resize(
    program_formula.no_globals,
    formula_container.gen_false());

  // initialize locals the same way
  
  thread.locals.resize(
    program_formula.no_locals,
    formula_container.gen_false());

  // initialize guard with *false*
  state.data_w().guard=formula_container.gen_false();

  return state;
}

/*******************************************************************\

Function: simulator_ctt::summarize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_ctt::summarize()
{
  // make first edge
  new_edge("main", make_initial_state());

  while(!active_edges.empty())
  {
    edget &edge=**active_edges.begin();
    
    while(!edge.queue.empty())
    {
      explore(edge.queue.next(), edge);
      if(error_state_found) return;
    }
    
    std::cout << "Finished edge for " << edge.function << std::endl;

    active_edges.erase(&edge);
  }
}
