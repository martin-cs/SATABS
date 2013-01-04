/*******************************************************************\

Module: Symbolic Simulator: State Data Structure

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include "state.h"

/*******************************************************************\

Function: statet::statet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

statet::statet():d(new state_dt)
{
}

/*******************************************************************\

Function: statet::statet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

statet::statet(const statet &s)
{
  assert(this!=&s);

  if(s.d==NULL)
    d=NULL;
  else
  {
    d=s.d;
    d->ref_count++;
  }
}

/*******************************************************************\

Function: statet::operator=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

statet &statet::operator=(const statet &s)
{
  assert(this!=&s);

  if(s.d==NULL)
  {
    d=NULL;
  }
  else
  {
    remove_ref(d);
    d=s.d;
    d->ref_count++;
  }

  return *this;
}

/*******************************************************************\

Function: statet::set_previous

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statet::set_previous(const statet &_state, unsigned thread)
{
  detatch();
  assert(thread<_state.d->threads.size());
  d->is_initial_state=false;
  d->previous_thread=thread;
  d->previous_PC=_state.d->threads[thread].PC;
  d->previous_program=_state.d->threads[thread].program;
  d->previous=_state;
}

/*******************************************************************\

Function: statet::statet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

statet::statet(state_dt *_d)
{
  d=_d;
  if(d!=NULL) d->ref_count++;
}

/*******************************************************************\

Function: statet::detatch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statet::detatch()
{
  assert(d!=NULL);
  if(d->ref_count>1)
  {
    state_dt *old_data(d);
    state_dt xx=*old_data;
    d=new state_dt(*old_data);
    d->ref_count=1;
    remove_ref(old_data);
    
    #if 0
    static unsigned count=0;
    count++;
    std::cout << "C:"  << count << std::endl;
    #endif
  }
}

/*******************************************************************\

Function: statet::remove_ref

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statet::remove_ref(state_dt *old_data)
{
  if(old_data==NULL) return;
  old_data->ref_count--;
  if(old_data->ref_count==0)
    delete old_data;
}

/*******************************************************************\

Function: statet::is_backwards_jump

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool statet::is_backwards_jump() const
{
  const state_dt &d=data();

  if(d.is_initial_state) return false;
  
  const_targett old_PC=d.previous_PC;
  const_targett new_PC=d.threads[d.previous_thread].PC;

  return old_PC->location_number>=new_PC->location_number;
}

/*******************************************************************\

Function: state_dt::state_dt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

state_dt::state_dt():is_initial_state(false), 
                     previous((state_dt *)0),
                     //nondet_count(0),
                     taken(false),
                     in_atomic_section(false),
                     ref_count(1)
{
}

/*******************************************************************\

Function: state_dt::~state_dt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

state_dt::~state_dt()
{
}

/*******************************************************************\

Function: alive

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool alive(
  const program_formulat &program_formula,
  const statet &state,
  unsigned v,
  unsigned t)
{
  if(program_formula.variables[v].is_global)
  {
    for(t=0; t<state.data().threads.size(); t++)
      if(!state.data().threads[t].is_at_end())
      {
        program_formulat::formula_goto_programt::const_targett PC=
          state.data().threads[t].PC;

        if(PC->code.alive.count(v)!=0)
          return true;
      }
  }
  else
  {
    if(!state.data().threads[t].is_at_end())
    {
      program_formulat::formula_goto_programt::const_targett PC=
        state.data().threads[t].PC;

      if(PC->code.alive.count(v)!=0)
        return true;
    }
  }

  return false;
}

/*******************************************************************\

Function: state_dt::build_choice

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void state_dt::build_choice(
  formula_containert &formula_container,
  formulat choice,
  const statet &other_state)
{
  const state_dt &other=other_state.data();

  // adjust guard
  guard=formula_container.gen_if(choice, guard, other.guard);
  
  // globals
  assert(globals.size()==other.globals.size());

  for(unsigned g=0; g<globals.size(); g++)
    globals[g]=formula_container.gen_if(choice, globals[g], other.globals[g]);
  
  assert(threads.size()==other.threads.size());
  
  // locals
  for(unsigned t=0; t<threads.size(); t++)
  {
    statet::threadt &thread=threads[t];
    const statet::threadt &other_thread=other.threads[t];
    
    assert(thread.locals.size()==other_thread.locals.size());
    
    for(unsigned l=0; l<thread.locals.size(); l++)
      thread.locals[l]=formula_container.gen_if(
        choice, thread.locals[l], other_thread.locals[l]);
  }
}

/*******************************************************************\

Function: state_dt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void state_dt::output(std::ostream &out) const
{
  // guard
  out << "Guard: ";
  guard.output(out);
  out << std::endl;
    
  // globals
  for(unsigned g=0; g<globals.size(); g++)
  {
    out << "G" << g << ":";
    globals[g].output(out);
    out << std::endl;
  }
  
  // locals
  for(unsigned t=0; t<threads.size(); t++)
  {
    const statet::threadt &thread=threads[t];
    
    for(unsigned l=0; l<thread.locals.size(); l++)
    {
      out << "T" << t << "L" << l << ": ";
      thread.locals[l].output(out);
      out << std::endl;
    }
  }
}
