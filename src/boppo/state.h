/*******************************************************************\

Module: Symbolic Simulator: State Data Structure

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BOPPO_STATE_H
#define CPROVER_BOPPO_STATE_H

#include <hash_cont.h>

#include "program_formula.h"

class statet
{
public:
  typedef program_formulat::formula_goto_programt programt;
  typedef const programt *programpt;
  typedef programt::targett targett;
  typedef programt::const_targett const_targett;
  
  typedef std::vector<formulat> valuest;

  struct threadt
  {
    valuest locals;
    const_targett PC;
    programpt program;
    
    // 'counter abstraction'
    bool multiple;
    
    threadt():multiple(false)
    {
    }
    
    inline bool is_at_end() const
    {
      return PC==program->instructions.end();
    }
    
    const_targett end_pc() const
    {
      return program->instructions.end();
    }

    const_targett start_pc() const
    {
      return program->instructions.begin();
    }
  };
  
  typedef std::vector<threadt> threadst;

  virtual ~statet() { remove_ref(d); }

  statet();

  statet(const statet &s);
  statet &operator=(const statet &s);

  void swap(statet &state)
  {
    std::swap(state.d, d);
  }
  
  void set_previous(const statet &_state, unsigned thread);
  
  statet(struct state_dt *_d);

  void detatch();
  
  bool is_null() const { return d==NULL; }

  struct state_dt &data_w() { detatch(); return *d; }
  const struct state_dt &data() const { return *d; }  

  bool is_backwards_jump() const;

protected:
  struct state_dt *d;
  void remove_ref(struct state_dt *old_data);
};

struct state_dt
{
public:
  // how did we get to this state?
  bool is_initial_state;
  unsigned previous_thread;
  statet::const_targett previous_PC;
  statet::programpt previous_program;
  statet previous;
  
  // is it a taken branch?
  bool taken;
  
  // the globals
  statet::valuest globals;

  // the threads
  statet::threadst threads;
  
  // can we be in this state?    
  formulat guard;
  
  // atomic?
  bool in_atomic_section;
  
  unsigned ref_count;

  unsigned number_of_threads() const
  {
    return threads.size();
  }
  
  formulat get_var(unsigned v, unsigned t) const
  {
    if(v<globals.size())
      return globals[v];
    
    v-=globals.size();
    assert(t<threads.size());
    assert(v<threads[t].locals.size());
    return threads[t].locals[v];
  }
  
  formulat get_var(unsigned v) const
  {
    assert(v<globals.size());
    return globals[v];
  }
  
  unsigned no_vars() const
  {
    assert(!threads.empty());
    return globals.size()+threads.front().locals.size();
  }

  void set_var(unsigned v, unsigned t, formulat f)
  {
    if(v<globals.size())
      globals[v]=f;
    else
    {
      v-=globals.size();
      assert(t<threads.size());
      assert(v<threads[t].locals.size());
      threads[t].locals[v]=f;
    }
  }

  void copy_PCs(std::vector<statet::const_targett> &PCs) const
  {
    PCs.resize(threads.size());
    for(unsigned t=0; t<PCs.size(); t++)
      PCs[t]=threads[t].PC;
  }
  
  bool compare_PCs(const std::vector<statet::const_targett> &PCs) const
  {
    assert(PCs.size()==threads.size());
    for(unsigned t=0; t<PCs.size(); t++)
      if(PCs[t]!=threads[t].PC)
        return false;
        
    return true;
  }

  state_dt();
  virtual ~state_dt();
  
  void build_choice(
    formula_containert &formula_container,
    formulat choice,
    const statet &other);
    
  void output(std::ostream &out) const;
};

bool alive(
  const program_formulat &program_formula,
  const statet &state,
  unsigned v,
  unsigned t);

#endif
