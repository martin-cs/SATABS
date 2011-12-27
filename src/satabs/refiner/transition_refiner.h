/*******************************************************************\

Module: Refiner

Author: Daniel Kroening

Date: June 2003

Purpose: Calculate predicates for predicate abstraction.

\*******************************************************************/

#ifndef CPROVER_SATABS_TRANSITION_REFINER_H
#define CPROVER_SATABS_TRANSITION_REFINER_H

#include "refiner.h"
#include "transition_cache.h"

class transition_refinert:public refinert
{
public:
  transition_refinert(
      const argst &args,
      bool _prefix_first,
      unsigned max_predicates_to_add,
      bool prefer_non_pointer_predicates,
      bool no_mixed_predicates,
      bool _passive_constrain):
    refinert(args, max_predicates_to_add,
        prefer_non_pointer_predicates, no_mixed_predicates),
    prefix_first(_prefix_first),
    passive_constrain(_passive_constrain)
  {
    stats.insert(std::make_pair(
          "Total transition refinements",
          statt(false, 0)));
    stats.insert(std::make_pair(
          "Transition refinement iterations",
          statt(false, 0)));
    stats.insert(std::make_pair(
          "Spurious guard transitions requiring more than 1 passive thread",
          statt(false, 0)));
    stats.insert(std::make_pair(
          "Invalid states requiring more than 1 passive thread",
          statt(false, 0)));
    stats.insert(std::make_pair(
          "Spurious assignment transitions requiring more than 1 passive thread",
          statt(false, 0)));
  }

  void refine(
    predicatest &predicates, 
    abstract_modelt &abstract_model,
    const fail_infot &fail_info);

protected:
  const bool prefix_first;
  const bool passive_constrain;
  
  // Updates the set of predicates for the same program according to
  // the counterexample. 
  virtual bool refine_prefix(
    predicatest &predicates, 
    abstract_modelt &abstract_model,
    const fail_infot &fail_info)
  {
    return true; // return error
  }

  virtual bool check_transitions(
    const predicatest &predicates, 
    abstract_modelt &abstract_model,
    const fail_infot &fail_info);

  virtual bool check_transition(
    const predicatest &preficates,
    const abstract_stept &abstract_state_from,
    const abstract_stept &abstract_state_to,
    bool &first_check);

  virtual bool check_assignment_transition(
    const predicatest &preficates,
    const abstract_stept &abstract_state_from,
    const abstract_stept &abstract_state_to,
    unsigned passive_id);

  virtual bool check_guarded_transition(
    const predicatest &preficates,
    const abstract_stept &abstract_state_from,
    unsigned passive_id,
    bool &inconsistent_initial_state);

  virtual void constrain_goto_transition(
    abstract_transition_relationt &abstract_transition_relation,
    const exprt &condition,
    bool negated);

  virtual void constrain_assume_transition(
    abstract_transition_relationt &abstract_transition_relation,
    const exprt &condition);

  transition_cachet transition_cache;
};

#endif
