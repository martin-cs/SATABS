/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simulator_ct.h"

/*******************************************************************\

Function: simulator_ctt::queuet::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_ctt::queuet::add(const statet &new_state)
{
  const statet::threadt &new_thread=new_state.data().threads.front();

  // first compute priority
  unsigned p=priority(new_state);

  unsigned ordering;
  
  if(new_thread.is_at_end())
    ordering=-1;
  else
    ordering=new_thread.PC->location_number;

  // build key
  keyt key(p, ordering);

  // look it up
  std::pair<mapt::iterator, bool> r=map.insert(
    std::pair<keyt, statet>(key, new_state));
  
  if(r.second) // really inserted?
    return; // yes, done

  std::cout << "MERGING!!!!!!!!!!!\n";
    
  // no, we already got one
  statet &old_state=r.first->second;  
  statet::threadt &old_thread=old_state.data_w().threads.front();

  // merge them!
  assert(old_thread.PC==new_thread.PC);

  formulat choice=formula_container.gen_nondet();
  
  old_state.data_w().build_choice(formula_container, choice, new_state);
}

/*******************************************************************\

Function: simulator_ctt::queuet::priority

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned simulator_ctt::queuet::priority(const statet &state)
{
  const statet::threadt &t=state.data().threads.front();

  // high number -> delay
  
  if(t.is_at_end())
    return 6;
  
  const instructiont &instruction=*t.PC;
  
  if(instruction.is_return())
    return 6;
  else if(instruction.is_function_call())
    return 5;
  else if(instruction.code.can_form_cycle)
    return 4;
  else if(instruction.is_goto())
    return 3;
  else if(instruction.is_assert())
    return 2;
  else
    return 1;
}

/*******************************************************************\

Function: operator <

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator < (
  const simulator_ctt::queuet::keyt &a,
  const simulator_ctt::queuet::keyt &b)
{
  if(a.priority<b.priority) return true;
  if(a.priority>b.priority) return false;
  return a.ordering>b.ordering;
  //return a.ordering<b.ordering;
}
