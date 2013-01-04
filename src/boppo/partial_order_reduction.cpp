/*******************************************************************\

Module: Compute Interleaving with Partial Order Reduction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <threeval.h>

#include "simulator.h"

/*******************************************************************\

Function: simulatort::compute_rw_sets

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::compute_rw_sets(
  const program_formulat::formula_goto_programt::instructiont
  &instruction,
  std::set<unsigned> &read,
  std::set<unsigned> &write)
{
  switch(instruction.type)
  {
  case GOTO:
  case ASSUME:
    // these two are dangerous!
    // as they are added to the guard, the effect is like writing!
    instruction.guard.get_global_variables(read, program_formula.variables);
    instruction.guard.get_global_variables(write, program_formula.variables);
    break;

  case ASSERT:
    // it reads the variables in the guard
    instruction.guard.get_global_variables(read, program_formula.variables);
    break;

  case ASSIGN:
    for(program_formulat::assignst::const_iterator
        it=instruction.code.assigns.begin();
        it!=instruction.code.assigns.end();
        it++)
    {
      if(program_formula.variables[it->variable].is_global)
        write.insert(it->variable);

      it->value.get_global_variables(
        read, program_formula.variables);
    }

    // the constraint is like an assume
    instruction.code.constraint.get_global_variables(read, program_formula.variables);
    instruction.code.constraint.get_global_variables(write, program_formula.variables);
    break;

  case OTHER:
    assert(false);
    break;

  case ATOMIC_BEGIN:
    // this one basically reads and writes all the globals
    for(unsigned v=0; v<program_formula.no_globals; v++)
    {
      write.insert(v);
      read.insert(v);
    }
    
    break;

  case DEAD:
  case SKIP:
  case LOCATION:
  case END_FUNCTION:
  case START_THREAD:
  case END_THREAD:
  case ATOMIC_END:
  case DECL:
    // these don't read or write
    break;

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: simulatort::partial_order_reduction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::partial_order_reduction(
  const statet &state,
  interleavingt &interleaving)
{
  if(interleaving.size()<2) return;
  
  const statet::threadst &threads=state.data().threads;

  for(interleavingt::const_iterator
      it=interleaving.begin();
      it!=interleaving.end();
      it++)
  {
    unsigned thread=*it;
    
    // get instruction
    const instructiont &instruction=*threads[thread].PC;
    
    // cycle condition
    if(instruction.is_goto())
    {
      if(!instruction.guard.is_true())
        continue;
        
      bool cycle=false;
    
      for(program_formulat::formula_goto_programt::
          instructiont::targetst::const_iterator
          t_it=instruction.targets.begin();
          t_it!=instruction.targets.end();
          t_it++)
        if((*t_it)->code.can_form_cycle)
        {
          cycle=true;
          break;
        }
        
      if(cycle) continue;
    }
    
    if(instruction.is_skip() ||
       instruction.is_location() ||
       instruction.is_end_function() ||
       instruction.is_start_thread() ||
       instruction.is_end_thread() ||
       instruction.is_atomic_end() ||
       (instruction.is_assume() &&
        instruction.guard.is_true()) ||
       (instruction.is_goto() &&
        instruction.guard.is_true()))
    {
      interleavingt new_interleaving;
      new_interleaving.push_back(thread);
      interleaving.swap(new_interleaving);
      return;
    }
  }
  
  // find dependencies

  // from threads to variables
  std::map<unsigned, std::set<unsigned> > t_r, t_w;  

  for(interleavingt::const_iterator
      it=interleaving.begin();
      it!=interleaving.end();
      it++)
  {
    unsigned thread=*it;
    
    // get instruction
    const instructiont &instruction=*threads[thread].PC;
    
    std::set<unsigned> read, write;
      
    compute_rw_sets(instruction, read, write);
    
    t_r[thread].insert(read.begin(), read.end());
    t_w[thread].insert(write.begin(), write.end());
  }
  
  for(interleavingt::const_iterator
      it=interleaving.begin();
      it!=interleaving.end();
      it++)
  {
    unsigned thread=*it;
    
    // get instruction
    const instructiont &instruction=*state.data().threads[thread].PC;
    
    // the thread must not affect enabledness
    if(instruction.is_goto() ||
       instruction.is_assume())
      continue;

    if(instruction.is_assign())
      if(!instruction.code.constraint.is_true())
        continue;

    const std::set<unsigned> &read=t_r[thread],
                             &write=t_w[thread];
                             
    // we want a thread that only reads
    if(!write.empty()) continue;

    // and please, noone else writes it
    std::set<unsigned> others_write;

    for(interleavingt::const_iterator
        o_it=interleaving.begin();
        o_it!=interleaving.end();
        o_it++)
    {
      unsigned o_thread=*o_it;
      if(o_thread!=thread)
      {
        const std::set<unsigned> &o_write=t_w[o_thread];
        others_write.insert(o_write.begin(), o_write.end());
      }
    }
    
    bool conflict=false;
    
    for(std::set<unsigned>::const_iterator s_it=read.begin();
        s_it!=read.end() && !conflict;
        s_it++)
    {
      const unsigned v=*s_it;
      if(others_write.find(v)!=others_write.end()) conflict=true; // somebody else writes
    }

    if(!conflict)
    {
      interleavingt new_interleaving;
      new_interleaving.push_back(thread);
      interleaving.swap(new_interleaving);
      return;
    }
  }  
}

/*******************************************************************\

Function: simulatort::compute_interleaving

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::compute_interleaving(
  const statet &state,
  interleavingt &interleaving)
{
  interleaving.clear();
  
  // see if we are in an atomic section
  if(state.data().in_atomic_section)
  {
    // if so, we stick to the thread we had before,
    // unless it's done
    assert(!state.data().is_initial_state);
    
    unsigned t=state.data().previous_thread;

    if(state.data().threads[t].is_at_end())
      return;

    interleaving.push_back(t);
    return;
  }

  // take all for now
  for(unsigned i=0; i<state.data().threads.size(); i++)
  {
    // end of thread?
    if(state.data().threads[i].is_at_end())
      continue;
      
    // get instruction
    //const instructiont &instruction=*state.data().threads[i].PC;
      
    interleaving.push_back(i);
  }
  
  // ok -- now do partial order reduction
  
  if(enable_partial_order_reduction)
    partial_order_reduction(state, interleaving);
}
