/*******************************************************************\

Module: Simulator

Author: Daniel Kroening
    
Date: October 2005

Purpose:

\*******************************************************************/

#include "transition_cache.h"

/*******************************************************************\

Function: transition_cachet::entryt::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void transition_cachet::entryt::build(
  const abstract_stept &abstract_state_from,
  const abstract_stept &abstract_state_to)
{
  pc=abstract_state_from.pc->code.concrete_pc;

  // from

  abstract_stept::thread_to_predicate_valuest::const_iterator from_predicates_for_active_thread = abstract_state_from.thread_states.find(abstract_state_from.thread_nr);
  assert(abstract_state_from.thread_states.end() != from_predicates_for_active_thread);

  const std::set<unsigned> &from_predicates=
    abstract_state_from.pc->code.get_transition_relation().from_predicates;

  for(std::set<unsigned>::const_iterator
      it=from_predicates.begin();
      it!=from_predicates.end();
      it++)
    from[*it]=from_predicates_for_active_thread->second[*it];

  // to

  // Note that we take "thread_nr" from "abstract_state_from", not from "abstract_state_to", as the "from" state determines which thread is executing
  abstract_stept::thread_to_predicate_valuest::const_iterator to_predicates_for_active_thread = abstract_state_to.thread_states.find(abstract_state_from.thread_nr);
  assert(abstract_state_to.thread_states.end() != to_predicates_for_active_thread);

  const std::set<unsigned> &to_predicates=
    abstract_state_from.pc->code.get_transition_relation().to_predicates;

  for(std::set<unsigned>::const_iterator
      it=to_predicates.begin();
      it!=to_predicates.end();
      it++)
    to[*it]=to_predicates_for_active_thread->second[*it];
}
