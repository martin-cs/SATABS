/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BOPPO_STATE_PROJECTION_H
#define CPROVER_BOPPO_STATE_PROJECTION_H

#include <hash_cont.h>

#include "queue.h"

class state_projectiont
{
public:
  typedef program_formulat::formula_goto_programt::targett targett;
  typedef program_formulat::formula_goto_programt::const_targett const_targett;

  state_projectiont(
    formula_containert &_formula_container,
    const program_formulat &_program_formula):
    formula_container(_formula_container),
    program_formula(_program_formula)
  {
  }

  void new_states(queuet &queue, bool use_cache);
  
protected:  
  formula_containert &formula_container;
  const program_formulat &program_formula;

  typedef std::list<statet> state_listt;
  
  typedef std::map<const_targett, state_listt> state_mapt;
  state_mapt state_map;
  
  bool is_new(const statet &state, bool use_cache);

  bool is_equal(
    const statet &old_state,
    const statet &new_state,
    bool use_cache);

  bool is_syntactically_equal(
    const statet &old_state,
    const statet &new_state);
};

#endif
