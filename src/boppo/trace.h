/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BOPPO_TRACE_H
#define CPROVER_BOPPO_TRACE_H

#include <list>

#include <threeval.h>

#include "program_formula.h"

class trace_stept
{
public:
  typet type;

  typedef program_formulat::formula_goto_programt::targett targett;
  typedef program_formulat::formula_goto_programt::const_targett const_targett;
  typedef program_formulat::formula_goto_programt::instructiont instructiont;

  typedef std::vector<const_targett> PCst;
  
  void copy_from(const statet &s)
  {
    is_initial_state=s.data().is_initial_state;
    previous_thread=s.data().previous_thread;
    previous_PC=s.data().previous_PC;
    previous_program=s.data().previous_program;
    is_error_state=false;
    state=s;
    
    threads.resize(s.data().threads.size());

    for(unsigned t=0; t<threads.size(); t++)
    {
      threads[t].PC=s.data().threads[t].PC;
    }
  }
  
  void convert(propt &prop)
  {
    const state_dt &d=state.data();

    global_literals.resize(d.globals.size());

    for(unsigned v=0; v<d.globals.size(); v++)
      global_literals[v]=d.globals[v].convert(prop);
      
    assert(threads.size()==d.threads.size());

    for(unsigned t=0; t<d.threads.size(); t++)
    {
      threadt &thread=threads[t];

      thread.local_literals.resize(d.threads[t].locals.size());

      for(unsigned v=0; v<thread.local_literals.size(); v++)
        thread.local_literals[v]=d.threads[t].locals[v].convert(prop);
    }  
  }
  
  void get_values(const propt &prop)
  {
    global_values.resize(global_literals.size());

    for(unsigned v=0; v<global_values.size(); v++)
    {
      tvt value=prop.l_get(global_literals[v]);
      global_values[v]=value.is_true();
    }

    for(unsigned t=0; t<threads.size(); t++)
      threads[t].get_values(prop);
  }

  // Boolean values of the global variables
  typedef std::vector<bool> valuest;
  typedef std::vector<literalt> literalst;

  valuest global_values;
  literalst global_literals;
  
  struct threadt
  {
    const_targett PC;
    valuest local_values;
    literalst local_literals;

    void get_values(const propt &prop)
    {
      local_values.resize(local_literals.size());
      for(unsigned v=0; v<local_values.size(); v++)
      {
        tvt value=prop.l_get(local_literals[v]);
        local_values[v]=value.is_true();
      }
    }
  };
  
  typedef std::vector<threadt> threadst;
  threadst threads;
  
  bool is_initial_state, is_error_state;
  unsigned previous_thread;

  const_targett previous_PC;
  statet::programpt previous_program;
  
  statet state;

  typedef std::list<class trace_stept>::iterator trace_itt;
  typedef std::list<trace_itt> loop_listt;

  // to where this state can loop back to and loop from
  loop_listt loop_to, loop_from;
  
  friend void add_loop(trace_itt from, trace_itt to)
  {
    // avoid duplicates
    for(loop_listt::const_iterator
        it=from->loop_to.begin();
        it!=from->loop_to.end();
        it++)
      if(*it==to)
        return;
    
    from->loop_to.push_back(to);
    to->loop_from.push_back(from);
  }
  
  trace_stept():
    is_initial_state(false),
    is_error_state(false),
    state(NULL) { }
    
  bool compare_PCs(const statet &s) const
  {
    const state_dt &d=s.data();
    if(d.threads.size()!=threads.size()) return false;
    
    for(unsigned t=0; t<threads.size(); t++)
      if(threads[t].PC!=d.threads[t].PC) return false;
      
    return true;
  }
};

typedef std::list<trace_stept> tracet;

#endif
