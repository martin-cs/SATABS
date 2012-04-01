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
    const abstract_stept &abstract_state_to,
    unsigned passive_id)
{
  // Note that we take "thread_nr" from "abstract_state_from", not from "abstract_state_to", as the "from" state determines which thread is executing
  const unsigned active_id=abstract_state_from.thread_nr;

  pc=abstract_state_from.pc->code.concrete_pc;

  // from

  abstract_stept::thread_to_predicate_valuest::const_iterator from_predicates_for_active_thread = abstract_state_from.thread_states.find(active_id);
  assert(abstract_state_from.thread_states.end() != from_predicates_for_active_thread);

  /*
     const std::set<unsigned> &from_predicates=
     abstract_state_from.pc->code.get_transition_relation().from_predicates;

     for(std::set<unsigned>::const_iterator
     it=from_predicates.begin();
     it!=from_predicates.end();
     it++)
     from[*it]=from_predicates_for_active_thread->second[*it];
     */
  from.resize(from_predicates_for_active_thread->second.size());
  unsigned i=0;
  for(abstract_stept::predicate_valuest::const_iterator
      it=from_predicates_for_active_thread->second.begin();
      it!=from_predicates_for_active_thread->second.end();
      ++it, ++i)
    from[i]=*it;

  // to

  abstract_stept::thread_to_predicate_valuest::const_iterator to_predicates_for_active_thread = abstract_state_to.thread_states.find(active_id);
  assert(abstract_state_to.thread_states.end() != to_predicates_for_active_thread);

  /*
     const std::set<unsigned> &to_predicates=
     abstract_state_from.pc->code.get_transition_relation().to_predicates;

     for(std::set<unsigned>::const_iterator
     it=to_predicates.begin();
     it!=to_predicates.end();
     it++)
     to[*it]=to_predicates_for_active_thread->second[*it];
     */
  to.resize(from_predicates_for_active_thread->second.size());
  i=0;
  for(abstract_stept::predicate_valuest::const_iterator
      it=to_predicates_for_active_thread->second.begin();
      it!=to_predicates_for_active_thread->second.end();
      ++it, ++i)
    to[i]=*it;

  if(passive_id != active_id)
  {
    // from

    abstract_stept::thread_to_predicate_valuest::const_iterator from_predicates_for_passive_thread =
      abstract_state_from.thread_states.find(passive_id);
    assert(abstract_state_from.thread_states.end() != from_predicates_for_passive_thread);

    from_passive.resize(from_predicates_for_passive_thread->second.size());
    unsigned i=0;
    for(abstract_stept::predicate_valuest::const_iterator
        it=from_predicates_for_passive_thread->second.begin();
        it!=from_predicates_for_passive_thread->second.end();
        ++it, ++i)
      from_passive[i]=*it;

    // to

    abstract_stept::thread_to_predicate_valuest::const_iterator to_predicates_for_passive_thread =
      abstract_state_to.thread_states.find(passive_id);
    assert(abstract_state_to.thread_states.end() != to_predicates_for_passive_thread);

    to_passive.resize(from_predicates_for_passive_thread->second.size());
    i=0;
    for(abstract_stept::predicate_valuest::const_iterator
        it=to_predicates_for_passive_thread->second.begin();
        it!=to_predicates_for_passive_thread->second.end();
        ++it, ++i)
      to_passive[i]=*it;

  }
}
