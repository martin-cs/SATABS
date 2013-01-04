/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include "state_projection.h"
#include "compare_states.h"

/*******************************************************************\

Function: state_projectiont::new_states

  Inputs:

 Outputs: return true iff there are new projected states

 Purpose:

\*******************************************************************/

void state_projectiont::new_states(queuet &queue, bool use_cache)
{
  // iterate over all states in queue

  #if 0  
  if(queue.new_threads_queue.empty()) return;
  
  for(state_listt::iterator it=queue.new_threads_queue.begin();
      it!=queue.new_threads_queue.end();
      it++)
  {
    if(is_new(*it, use_cache))
    {
      queue.main_queue.push_back(statet());
      queue.main_queue.back().swap(*it);
    }
  }
  
  queue.new_threads_queue.clear();
  
  if(queue.main_queue.empty())
    std::cout << "Thread fixed-point reached" << std::endl;
  else
    std::cout << "Increasing number of threads" << std::endl;
  #endif
}

/*******************************************************************\

Function: state_projectiont::is_new

  Inputs:

 Outputs: return true iff projected state is new

 Purpose:

\*******************************************************************/

bool state_projectiont::is_new(const statet &state, bool use_cache)
{
  // get the right map
  assert(!state.data().previous.is_null());
  
  state_listt &state_list=
    state_map[state.data().previous_PC];

  // first try syntactically
  
  for(state_listt::const_iterator
      it=state_list.begin();
      it!=state_list.end();
      it++)
    if(is_syntactically_equal(*it, state))
      return false; // not new
      
  // now try expensive comparison

  for(state_listt::const_iterator
      it=state_list.begin();
      it!=state_list.end();
      it++)
    if(is_equal(*it, state, use_cache))
    {
      // put into list anyways
      state_list.push_back(state);
      return false; // not new
    }

  // not found, it's new  
  state_list.push_back(state);
  
  return true;
}

/*******************************************************************\

Function: state_projectiont::is_equal

  Inputs:

 Outputs: return true iff projected states are equivalent

 Purpose:

\*******************************************************************/

bool state_projectiont::is_equal(
  const statet &old_state,
  const statet &new_state,
  bool use_cache)
{
  std::set<vart> vars;

  unsigned v=0;
  
  for(program_formulat::variablest::const_iterator
      it=program_formula.variables.begin();
      it!=program_formula.variables.end();
      it++, v++)
    if(it->is_global)
      vars.insert(vart(v));

  return compare_states(formula_container, new_state, old_state, vars, use_cache);
}

/*******************************************************************\

Function: state_projectiont::is_syntactically_equal

  Inputs:

 Outputs: return true iff projected states are equivalent

 Purpose:

\*******************************************************************/

bool state_projectiont::is_syntactically_equal(
  const statet &old_state,
  const statet &new_state)
{
  if(old_state.data().guard!=new_state.data().guard)
    return false;
  
  unsigned v=0;
  
  for(program_formulat::variablest::const_iterator
      it=program_formula.variables.begin();
      it!=program_formula.variables.end();
      it++, v++)
  {
    if(it->is_global)
    {
      assert(v<old_state.data().globals.size());
      assert(v<new_state.data().globals.size());

      if(old_state.data().globals[v]!=
         new_state.data().globals[v])
        return false;
    }
  }
  
  return true;  
}
