/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BOPPO_HISTORY_H
#define CPROVER_BOPPO_HISTORY_H

#include <hash_cont.h>

#include "state.h"

class historyt
{
public:
  typedef program_formulat::formula_goto_programt::targett targett;
  typedef program_formulat::formula_goto_programt::const_targett const_targett;
  typedef std::vector<const_targett> PCst;
  
  historyt(
    formula_containert &_formula_container,
    program_formulat &_program_formula):
    formula_container(_formula_container),
    program_formula(_program_formula)
  {
  }

  bool check_history(
    const statet &state,
    bool use_cache,
    bool enable_small_history);
  
protected:
  formula_containert &formula_container;
  const program_formulat &program_formula;

  class keyt
  {
  public:
    PCst PCs;

    void from_state(const statet &state)
    {
      state.data().copy_PCs(PCs);
    }
  };
  
  friend bool operator==(const keyt &a, const keyt &b);

  struct key_hash
  {
    size_t operator()(const keyt &key) const;
  };

  typedef std::list<statet> entry_listt;

  typedef hash_map_cont<keyt, entry_listt, key_hash> history_mapt;
  history_mapt history_map;
  
  bool compare_history(const statet &state, const statet &entry, bool use_cache);

  bool small_history(const statet &state, bool enable_small_history);
};

#endif
