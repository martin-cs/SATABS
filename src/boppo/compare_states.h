/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BOPPO_COMPARE_STATES_H
#define CPROVER_BOPPO_COMPARE_STATES_H

#include "state.h"

struct vart
{
  unsigned var_nr;
  unsigned thread_nr;
  bool is_global;

  friend bool operator<(const vart &a, const vart &b)
  {
    if(a.var_nr<b.var_nr) return true;
    if(a.var_nr>b.var_nr) return false;
    return a.thread_nr<b.thread_nr;
  }
  
  vart(unsigned _var_nr):var_nr(_var_nr), thread_nr(0), is_global(true)
  {
  }

  vart(unsigned _var_nr, unsigned _thread_nr):
    var_nr(_var_nr), thread_nr(_thread_nr), is_global(false)
  {
  }
};

bool compare_states(
  formula_containert &formula_container,
  const statet &state,
  const statet &entry,
  const std::set<vart> &vars,
  bool use_cache);

#endif
