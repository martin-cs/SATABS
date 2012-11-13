/*******************************************************************\

Module: Predicate Refinement for CEGAR

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#include <cassert>
#include <algorithm>
#include <iostream>

#include <expr_util.h>
#include <std_types.h>
#include <std_expr.h>
#include <simplify_expr.h>
#include <i2string.h>
#include <threeval.h>

#include <langapi/language_util.h>

#include <solvers/sat/cnf_clause_list.h>
#include <solvers/sat/satcheck_minisat2.h>

#include "../abstractor/predabs_aux.h"
#include "../simulator/simulator_sat_dec.h"
#include "../simulator/fail_info.h"
#include "../abstractor/predicates.h"
#include "../prepare/concrete_model.h"

#include "transition_refiner.h"

//#define DEBUG

/*******************************************************************\

Function: transition_refinert::refine

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void transition_refinert::refine(
    predicatest &predicates, 
    abstract_modelt &abstract_model,
    const fail_infot &fail_info)
{
  bool error;

  if(prefix_first)
  {
    error=refine_prefix(
        predicates,
        abstract_model,
        fail_info);

    if(error)
      error=check_transitions(
          predicates,
          abstract_model,
          fail_info);
  }
  else
  {  
    error=check_transitions(
        predicates,
        abstract_model,
        fail_info);

    if(error)
      error=refine_prefix(
          predicates,
          abstract_model,
          fail_info);
  }

  if(error)
  {
    // dump the CE

    for(abstract_counterexamplet::stepst::const_iterator
        it=fail_info.steps.begin();
        it!=fail_info.steps.end();
        it++)
      std::cout << *it;

    std::cout << std::endl;

    // dump the predicates
    std::cout << "Predicates:" << std::endl;

    for(unsigned p=0; p<predicates.size(); p++)
    {
      std::cout << "P" << p << ": "
        << from_expr(concrete_model.ns, "", predicates[p])
        << std::endl;
      //std::cout << "      " << predicates[p] << std::endl;
    }
    std::cout << std::endl;

    throw "refinement failure";
  }
}

/*******************************************************************\

Function: transition_refinert::check_transitions

Inputs:

Outputs:

Purpose: fix spurious transition

\*******************************************************************/

bool transition_refinert::check_transitions(
    const predicatest &predicates, 
    abstract_modelt &abstract_model,
    const fail_infot &fail_info)
{
  status("Checking transitions");

  bool error=true;

  abstract_counterexamplet::stepst::const_iterator previous;

  bool first_state=true;
  bool first_check=true;

  for(abstract_counterexamplet::stepst::const_iterator
      it=fail_info.steps.begin();
      it!=fail_info.steps.end();
      it++)
  {
    if(!it->is_state())
      continue;

    if(first_state)
      first_state=false;
    else
    {
      if(check_transition(
            predicates,
            *previous, *it, first_check))
        error=false;
    }

    // skip transition if path slicer tells us so
    if(!it->relevant)
    {
#ifdef DEBUG
      std::cout << "Skipping L" << it->label_nr << std::endl;
      it->output (std::cout);
#endif

      do
      { 
        it++;
      }
      while(!it->is_state() && it!=fail_info.steps.end());
    }

    if(it==fail_info.steps.end())
      break;

    previous=it;
  }

  if(error)
    status("Transitions are not spurious");
  else
  {
    status("Found a spurious transition");
    const std::string opt="Transition refinement iterations";
    assert(stats.find(opt)!=stats.end());
    ++(stats[opt].val);
  }

  return error;
}

/*******************************************************************\

Function: transition_refinert::check_transition

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool transition_refinert::check_transition(
    const predicatest &predicates,
    const abstract_stept &abstract_state_from,
    const abstract_stept &abstract_state_to,
    bool &first_check)
{

  // get the concrete basic block
  const goto_programt::instructiont &c_instruction=
    *abstract_state_from.pc->code.concrete_pc;

#ifdef DEBUG
  std::cout << "transition_refinert::check_transition_async: "
    << c_instruction.location << std::endl;
#endif

#ifdef DEBUG
  std::cout << "checking transition from label L" << 
    abstract_state_from.label_nr << " to label L" << 
    abstract_state_to.label_nr << std::endl;
#endif
#ifdef DEBUG
  ::std::cout << abstract_state_from << ::std::endl;
  goto_programt tmp;
  tmp.output_instruction(concrete_model.ns, "", std::cout, abstract_state_from.pc->code.concrete_pc);
  ::std::cout << abstract_state_to << ::std::endl;
#endif

  if(c_instruction.is_skip() ||
      c_instruction.is_location() ||
      c_instruction.is_end_function())
    return false; // ok

  if(c_instruction.is_other() && c_instruction.code.is_nil())
    return false; // ok

  // if all the predicates have fixed values, it can't be wrong
  // unless where we come from an inconsistent state.
  // thus, check the first time
  abstract_transition_relationt &abstract_transition_relation=
    abstract_state_from.pc->code.get_transition_relation();

  if(!c_instruction.is_goto() &&
      !c_instruction.is_assume() &&
      !c_instruction.is_assert())
  {
    if(!abstract_transition_relation.has_predicates())
    {
      print(9, "no predicates to check");
      return false; // ok
    }

    if(abstract_transition_relation.is_skip())
    {
      print(9, "Transition is skip");
      return false; // ok
    }
  }

  {
    for(abstract_stept::thread_to_predicate_valuest::const_iterator
        it = abstract_state_from.thread_states.begin();
        it != abstract_state_from.thread_states.end(); ++it)
      assert(it->second.size()==predicates.size());

    for(abstract_stept::thread_to_predicate_valuest::const_iterator
        it = abstract_state_to.thread_states.begin();
        it != abstract_state_to.thread_states.end(); ++it)
      assert(it->second.size()==predicates.size());
  }

  // For each (passive) thread, check that active transition is OK in context of
  // (a passive) thread's state, and passive transition (if there is one because
  // of a broadcast) is also OK
  // at last also check all passive threads, hence the <= comparison, a bit of a
  // hack
  for(unsigned int passive_id = 0;
      passive_id <= abstract_state_from.thread_states.size();
      passive_id++)
  {
    if(!passive_constrain &&
        passive_id != abstract_state_from.thread_nr)
      continue;

    // only check all passive threads if we have more than 1
    if(passive_id == abstract_state_from.thread_states.size() &&
        passive_id <= 2)
      continue;

    transition_cachet::entryt transition_cache_entry;
    if(passive_id < abstract_state_from.thread_states.size())
    {
      // check cache if this is a local check
      transition_cache_entry.build(
          abstract_state_from,
          abstract_state_to,
          passive_id);

      if(transition_cache.in_cache(transition_cache_entry))
      {
        print(9, "Transition is in cache");
        continue;
      }
    }

    bool inconsistent_initial_state=false;
    if(!c_instruction.is_other() &&
        !c_instruction.is_function_call() &&
        !c_instruction.is_return() &&
        !c_instruction.is_assign() &&
        !c_instruction.is_decl())
    {
      if(passive_id < abstract_state_from.thread_states.size())
      {
        abstract_stept::thread_to_predicate_valuest::const_iterator
          from_predicates_for_active_thread =
          abstract_state_from.thread_states.find(passive_id),
          to_predicates_for_active_thread =
            abstract_state_to.thread_states.find(passive_id);
        assert(abstract_state_from.thread_states.end() != from_predicates_for_active_thread);
        assert(abstract_state_to.thread_states.end() != to_predicates_for_active_thread);
        for(unsigned i=0; i < predicates.size(); ++i)
          assert(from_predicates_for_active_thread->second[i] ==
              to_predicates_for_active_thread->second[i]);
      }

      if(check_guarded_transition(predicates,
            abstract_state_from,
            passive_id,
            inconsistent_initial_state))
      {
        const std::string opt="Total transition refinements";
        assert(stats.find(opt)!=stats.end());
        ++(stats[opt].val);
        return true;
      }
    }
    else
    {
      if(check_assignment_transition(predicates,
            abstract_state_from,
            abstract_state_to,
            passive_id))
      {
        const std::string opt="Total transition refinements";
        assert(stats.find(opt)!=stats.end());
        ++(stats[opt].val);
        return true;
      }
    }

    if(!inconsistent_initial_state &&
        passive_id < abstract_state_from.thread_states.size())
      transition_cache.insert(transition_cache_entry);
  }

  return false;

}

/*******************************************************************\

Function: transition_refinert::check_assignment_transitions

Inputs:

Outputs:

Purpose: fix spurious assignment transition

\*******************************************************************/

bool transition_refinert::check_assignment_transition(
    const predicatest &predicates,
    const abstract_stept &abstract_state_from,
    const abstract_stept &abstract_state_to,
    unsigned passive_id)
{
  // Note that we take "thread_nr" from "abstract_state_from", not from "abstract_state_to", as the "from" state determines which thread is executing
  const unsigned active_id=abstract_state_from.thread_nr;
  const unsigned num_threads=abstract_state_from.thread_states.size();

  std::vector<predicatest> active_passive_preds(num_threads, predicatest());
  std::vector<std::vector<exprt> > predicates_wp(num_threads,
      std::vector<exprt>());
  std::list<exprt> constraints;

  for(unsigned int t=0; t < num_threads; ++t)
  {
    if(active_id!=t &&
        passive_id < num_threads &&
        t!=passive_id)
      continue;

    for(unsigned int i = 0; i < predicates.size(); i++)
    {
      active_passive_preds[t].lookup(active_id==t?
          predicates[i] :
          predicatest::make_expr_passive(predicates[i], concrete_model.ns, t));
    }
    assert(active_passive_preds[t].size() == predicates.size());

    std::list<exprt> constraints_t;
    build_equation(
        concrete_model.ns,
        active_passive_preds[t],
        abstract_state_from.pc->code.concrete_pc,
        constraints_t,
        predicates_wp[t]);

    constraints.splice(constraints.end(), constraints_t);
  }

  // create SAT solver object
  cnf_clause_listt cnf;
  bv_pointerst solver(concrete_model.ns, cnf);
  solver.unbounded_array=boolbvt::U_NONE;

  // convert constraints
  for(std::list<exprt>::const_iterator
      it=constraints.begin();
      it!=constraints.end();
      it++)
  {
    exprt tmp(*it);
    solver.set_to_true(tmp);
  }

  abstract_transition_relationt &abstract_transition_relation=
    abstract_state_from.pc->code.get_transition_relation();

  std::vector<std::vector<literalt> >
    predicate_variables_from(num_threads, std::vector<literalt>(predicates.size(), literalt())),
    predicate_variables_to(num_threads, std::vector<literalt>(predicates.size(), literalt()));

  bvt assumptions;

  std::vector<abstract_stept::thread_to_predicate_valuest::const_iterator>
    from_predicates(num_threads, abstract_state_from.thread_states.end()),
    to_predicates(num_threads, abstract_state_to.thread_states.end());
  for(unsigned int t=0; t < num_threads; ++t)
  {
    from_predicates[t]=abstract_state_from.thread_states.find(t);
    assert(abstract_state_from.thread_states.end() != from_predicates[t]);
    to_predicates[t]=abstract_state_to.thread_states.find(t);
    assert(abstract_state_to.thread_states.end() != to_predicates[t]);
  }

  // we use all predicates in order to also find constraints over invalid
  // from/to states
  for(unsigned i=0; i < predicates.size(); ++i)
  {
    assert(abstract_transition_relation.to_predicates.find(i) !=
        abstract_transition_relation.to_predicates.end() ||
        abstract_transition_relation.from_predicates.find(i) !=
        abstract_transition_relation.from_predicates.end() ||
        (from_predicates[active_id]->second[i] ==
         to_predicates[active_id]->second[i] &&
         (passive_id >= num_threads ||
          from_predicates[passive_id]->second[i] ==
          to_predicates[passive_id]->second[i])));

    for(unsigned int t=0; t < num_threads; ++t)
    {
      if(active_id!=t &&
          passive_id < num_threads &&
          t!=passive_id)
        continue;
      // not sure whether we really want the following check
      if(active_id!=t &&
          active_passive_preds[t][i]==predicates[i])
        continue;

      literalt li=make_pos(concrete_model.ns, solver, active_passive_preds[t][i]);
      predicate_variables_from[t][i]=li;

      assumptions.push_back(li.cond_negation(
            !from_predicates[t]->second[i]));

#ifdef DEBUG
      const std::string predname=
        (active_id==t?"P#":"PP"+i2string(t)+"#")+i2string(i);
      std::cerr
        << "F: " << predname << ": "
        << (from_predicates[t]->second[i]?"":"!") << "("
        << from_expr(concrete_model.ns, "", active_passive_preds[t][i]) << ")" << std::endl;
#endif

      literalt lo=make_pos(concrete_model.ns, solver, predicates_wp[t][i]);
      predicate_variables_to[t][i]=lo;

      assumptions.push_back(lo.cond_negation(
            !to_predicates[t]->second[i]));

#ifdef DEBUG
      std::cerr
        << "T: " << predname << ": "
        << (to_predicates[t]->second[i]?"":"!") << "("
        << from_expr(concrete_model.ns, "", predicates_wp[t][i]) << ")" << std::endl;
#endif
    }
  }

  satcheckt satcheck;
  cnf.copy_to(satcheck);
  satcheck.set_assumptions(assumptions);

  // solve it
  if(is_satisfiable(satcheck))
  {
    print(9, "Transition is OK");
#ifdef DEBUG
    std::cout << "********\n";
    solver.print_assignment(std::cout);
    std::cout << "********\n";
#endif
    return false; // ok
  }

  if(passive_id >= num_threads)
  {
    const std::string opt="Spurious assignment transitions requiring more than 1 passive thread";
    assert(stats.find(opt)!=stats.end());
    ++(stats[opt].val);
    return false; // can't do anything
  }

  print(9, "Assignment transition is spurious, refining");

  exprt constraint;

  for(unsigned i=0; i < predicates.size(); ++i)
  {
    if(satcheck.is_in_conflict(predicate_variables_from[active_id][i]))
    {
      constraint.operands().push_back(exprt());
      exprt &e=constraint.operands().back();
      e=exprt(ID_predicate_symbol, bool_typet());
      e.set(ID_identifier, i);
      if(from_predicates[active_id]->second[i]) e.make_not();
#ifdef DEBUG
      std::cout << "C-F: " << from_expr(concrete_model.ns, "", e) << std::endl;
#endif
    }

    if(passive_id!=active_id &&
        satcheck.is_in_conflict(predicate_variables_from[passive_id][i]))
    {
      constraint.operands().push_back(exprt());
      exprt &e=constraint.operands().back();
      e=exprt(ID_predicate_passive_symbol, bool_typet());
      e.set(ID_identifier, i);
      if(from_predicates[passive_id]->second[i]) e.make_not();
#ifdef DEBUG
      std::cout << "C-F: " << from_expr(concrete_model.ns, "", e) << std::endl;
#endif
    }

    if(satcheck.is_in_conflict(predicate_variables_to[active_id][i]))
    {
      constraint.operands().push_back(exprt());
      exprt &e=constraint.operands().back();
      e=exprt(ID_predicate_next_symbol, bool_typet());
      e.set(ID_identifier, i);
      if(to_predicates[active_id]->second[i]) e.make_not();
#ifdef DEBUG
      std::cout << "C-T: " << from_expr(concrete_model.ns, "", e) << std::endl;
#endif
    }

    if(passive_id!=active_id &&
        satcheck.is_in_conflict(predicate_variables_to[passive_id][i]))
    {
      constraint.operands().push_back(exprt());
      exprt &e=constraint.operands().back();
      e=exprt(ID_next_symbol, bool_typet());
      e.operands().resize(1);
      e.op0()=exprt(ID_predicate_passive_symbol, bool_typet());
      e.op0().set(ID_identifier, i);
      if(to_predicates[passive_id]->second[i]) e.make_not();
#ifdef DEBUG
      std::cout << "C-T: " << from_expr(concrete_model.ns, "", e) << std::endl;
#endif
    }
  }
#ifdef DEBUG
  ::std::cerr << "Spurious in thread " << passive_id << " (active: " << abstract_state_from.thread_nr << "): " << ::std::endl;
  ::std::cerr << abstract_state_from << ::std::endl;
  goto_programt tmp;
  tmp.output_instruction(concrete_model.ns, "", std::cerr, abstract_state_from.pc->code.concrete_pc);
  ::std::cerr << abstract_state_to << ::std::endl;
#endif

  if(constraint.operands().empty())
    constraint.make_false(); // this can happen if
  else                       // the invariants are inconsistent
    gen_or(constraint);

  // monotonicity-preserving refinement
  if(monotone_constrain &&
      !constraint.is_false() &&
      passive_id!=active_id && passive_id<num_threads)
  {
    and_exprt monotone;
    monotone.reserve_operands(2*2*predicates.size()+2);

    // first enumerate the solutions for the active thread, such that some
    // consistent transition over the passive threads exists
    {
      or_exprt big_or1;

#ifdef SATCHECK_MINISAT2
      satcheck_minisat_no_simplifiert satcheck2;
#else
      satcheckt satcheck2;
#endif
      cnf.copy_to(satcheck2);

      while(is_satisfiable(satcheck2))
      {
        bvt new_clause;
        new_clause.reserve(2*predicates.size());

        exprt::operandst new_constraint_ops;
        new_constraint_ops.reserve(2*predicates.size());

        for(unsigned i=0; i < predicates.size(); ++i)
        {
          const literalt &l=predicate_variables_from[active_id][i];
// #ifdef SATCHECK_MINISAT2
//           if(satcheck2.is_eliminated(l))
//             continue;
// #endif
          tvt sol=satcheck2.l_get(l);
          assert(sol.is_known());
          new_clause.push_back(l.cond_negation(sol.is_true()));

          new_constraint_ops.push_back(exprt());
          exprt &e=new_constraint_ops.back();
          e=exprt(ID_predicate_symbol, bool_typet());
          e.set(ID_identifier, i);
          if(sol.is_true()==l.sign()) e.make_not();
        }

        for(unsigned i=0; i < predicates.size(); ++i)
        {
          const literalt &l=predicate_variables_to[active_id][i];
// #ifdef SATCHECK_MINISAT2
//           if(satcheck2.is_eliminated(l))
//             continue;
// #endif
          tvt sol=satcheck2.l_get(l);
          assert(sol.is_known());
          new_clause.push_back(l.cond_negation(sol.is_true()));

          new_constraint_ops.push_back(exprt());
          exprt &e=new_constraint_ops.back();
          e=exprt(ID_predicate_next_symbol, bool_typet());
          e.set(ID_identifier, i);
          if(sol.is_true()==l.sign()) e.make_not();
        }

        and_exprt a(new_constraint_ops);
#ifdef DEBUG
        std::cout << "solution: " << from_expr(concrete_model.ns, "", a) << std::endl;
#endif
        big_or1.move_to_operands(a);

        satcheck2.lcnf(new_clause);
      }

      // at least one active transition must be possible
      assert(!big_or1.operands().empty());

      monotone.move_to_operands(big_or1);
    }

    // all passive predicates unchanged
    for(unsigned i=0; i < predicates.size(); ++i)
    {
      exprt bp(ID_predicate_passive_symbol, bool_typet());
      bp.set(ID_identifier, i);

      exprt bp_primed(ID_next_symbol, bool_typet());
      bp_primed.copy_to_operands(exprt(ID_predicate_passive_symbol, bool_typet()));
      bp_primed.op0().set(ID_identifier, i);

      or_exprt o1(not_exprt(bp), bp_primed);
      or_exprt o2(bp, not_exprt(bp_primed));
#ifdef DEBUG
      std::cout << "passive-eq: " << from_expr(concrete_model.ns, "", o1) << std::endl;
      std::cout << "passive-eq: " << from_expr(concrete_model.ns, "", o2) << std::endl;
#endif
      monotone.move_to_operands(o1);
      monotone.move_to_operands(o2);
    }

    // enumerate the solutions such that the passive thread cannot make a
    // transition
    {
      or_exprt big_or2;

#ifdef SATCHECK_MINISAT2
      satcheck_minisat_no_simplifiert satcheck2;
#else
      satcheckt satcheck2;
#endif
      cnf.copy_to(satcheck2);

      bvt clause;
      clause.reserve(3*predicates.size());
      for(unsigned i=0; i < predicates.size(); ++i)
      {
        clause.push_back(predicate_variables_from[active_id][i].negation());
        clause.push_back(predicate_variables_to[active_id][i].negation());
        clause.push_back(predicate_variables_from[passive_id][i].negation());
      }
      satcheck2.lcnf(clause);

      while(is_satisfiable(satcheck2))
      {
        bvt new_clause;
        new_clause.reserve(3*predicates.size());

        exprt::operandst new_constraint_ops;
        new_constraint_ops.reserve(3*predicates.size());

        for(unsigned i=0; i < predicates.size(); ++i)
        {
          const literalt &l=predicate_variables_from[active_id][i];
// #ifdef SATCHECK_MINISAT2
//           if(satcheck2.is_eliminated(l))
//             continue;
// #endif
          tvt sol=satcheck2.l_get(l);
          assert(sol.is_known());
          new_clause.push_back(l.cond_negation(sol.is_true()));

          new_constraint_ops.push_back(exprt());
          exprt &e=new_constraint_ops.back();
          e=exprt(ID_predicate_symbol, bool_typet());
          e.set(ID_identifier, i);
          if(sol.is_true()==l.sign()) e.make_not();
        }

        for(unsigned i=0; i < predicates.size(); ++i)
        {
          const literalt &l=predicate_variables_to[active_id][i];
// #ifdef SATCHECK_MINISAT2
//           if(satcheck2.is_eliminated(l))
//             continue;
// #endif
          tvt sol=satcheck2.l_get(l);
          assert(sol.is_known());
          new_clause.push_back(l.cond_negation(sol.is_true()));

          new_constraint_ops.push_back(exprt());
          exprt &e=new_constraint_ops.back();
          e=exprt(ID_predicate_next_symbol, bool_typet());
          e.set(ID_identifier, i);
          if(sol.is_true()==l.sign()) e.make_not();
        }

        for(unsigned i=0; i < predicates.size(); ++i)
        {
          const literalt &l=predicate_variables_from[passive_id][i];
// #ifdef SATCHECK_MINISAT2
//           if(satcheck2.is_eliminated(l))
//             continue;
// #endif
          tvt sol=satcheck2.l_get(l);
          assert(sol.is_known());
          new_clause.push_back(l.cond_negation(sol.is_true()));

          new_constraint_ops.push_back(exprt());
          exprt &e=new_constraint_ops.back();
          e=exprt(ID_predicate_passive_symbol, bool_typet());
          e.set(ID_identifier, i);
          if(sol.is_true()==l.sign()) e.make_not();
        }

        and_exprt a(new_constraint_ops);
#ifdef DEBUG
        std::cout << "solution no-passive-succ: " << from_expr(concrete_model.ns, "", a) << std::endl;
#endif
        big_or2.move_to_operands(a);

        satcheck2.lcnf(new_clause);
      }

      if(big_or2.operands().empty())
        monotone.operands().clear();
      else
        monotone.move_to_operands(big_or2);
    }

    constraint.move_to_operands(monotone);
  }

  abstract_transition_relation.constraints.push_back(constraint);

  // spurious!
  return true;
}

/*******************************************************************\

Function: transition_refinert::check_guarded_transitions

Inputs:

Outputs:

Purpose: fix spurious guarded transition

\*******************************************************************/

bool transition_refinert::check_guarded_transition(
    const predicatest &predicates,
    const abstract_stept &abstract_state_from,
    unsigned passive_id,
    bool &inconsistent_initial_state)
{
  // get the concrete basic block
  const goto_programt::instructiont &c_instruction=
    *abstract_state_from.pc->code.concrete_pc;

  if (!c_instruction.is_goto() &&
      !c_instruction.is_assume())
    return false; // whatever

  // this is the original guard
  exprt guard=c_instruction.guard; 

  if(guard.is_true()) // boring
    return false;

  // we might need to negate it if the branch was not taken
  if (c_instruction.is_goto() && 
      !abstract_state_from.branch_taken)
    guard.make_not();

  abstract_transition_relationt &abstract_transition_relation=
    abstract_state_from.pc->code.get_transition_relation();

#ifdef SATCHECK_MINISAT2
  satcheck_minisat_no_simplifiert satcheck;
#else
  satcheckt satcheck;
#endif
  bv_pointerst solver(concrete_model.ns, satcheck);
  solver.unbounded_array=boolbvt::U_NONE;

  // Note that we take "thread_nr" from "abstract_state_from", not from "abstract_state_to", as the "from" state determines which thread is executing
  const unsigned active_id=abstract_state_from.thread_nr;
  const unsigned num_threads=abstract_state_from.thread_states.size();

  std::vector<predicatest> active_passive_preds(num_threads, predicatest());

  for(unsigned int t=0; t < num_threads; ++t)
  {
    if(active_id!=t &&
        passive_id < num_threads &&
        t!=passive_id)
      continue;

    for(unsigned int i = 0; i < predicates.size(); i++)
    {
      active_passive_preds[t].lookup(active_id==t?
          predicates[i] :
          predicatest::make_expr_passive(predicates[i], concrete_model.ns, t));
    }
    assert(active_passive_preds[t].size() == predicates.size());
  }

  std::vector<std::vector<literalt> >
    predicate_variables_from(num_threads, std::vector<literalt>(predicates.size(), literalt()));

  bvt assumptions;

  std::vector<abstract_stept::thread_to_predicate_valuest::const_iterator>
    from_predicates(num_threads, abstract_state_from.thread_states.end());
  for(unsigned int t=0; t < num_threads; ++t)
  {
    from_predicates[t]=abstract_state_from.thread_states.find(t);
    assert(abstract_state_from.thread_states.end() != from_predicates[t]);
  }

  // we use all predicates in order to also find constraints over invalid
  // from states
  for(unsigned i=0; i < predicates.size(); ++i)
  {
    for(unsigned int t=0; t < num_threads; ++t)
    {
      if(active_id!=t &&
          passive_id < num_threads &&
          t!=passive_id)
        continue;
      // not sure whether we really want the following check
      if(active_id!=t &&
          active_passive_preds[t][i]==predicates[i])
        continue;

      literalt li=make_pos(concrete_model.ns, solver, active_passive_preds[t][i]);
      predicate_variables_from[t][i]=li;

      assumptions.push_back(li.cond_negation(
            !from_predicates[t]->second[i]));

#ifdef DEBUG
      const std::string predname=
        (active_id==t?"P#":"PP"+i2string(t)+"#")+i2string(i);
      std::cerr
        << "G-F: " << predname << ": "
        << (from_predicates[t]->second[i]?"":"!") << "("
        << from_expr(concrete_model.ns, "", active_passive_preds[t][i]) << ")" << std::endl;
#endif
    }
  }

  satcheck.set_assumptions(assumptions);

  if(!is_satisfiable(solver))
  {
    if(passive_id >= num_threads)
    {
      const std::string opt="Invalid states requiring more than 1 passive thread";
      assert(stats.find(opt)!=stats.end());
      ++(stats[opt].val);
    }
    inconsistent_initial_state = true;
    print(9, "Guarded transition spurious due to invalid abstract state");
    return false; // this has to be fixed in the respective assignment
  }

  // now add the guard
  solver.set_to_true(guard);

  // solve it incrementally
  if(is_satisfiable(solver))
  {
    print(9, "Transition is OK");
#ifdef DEBUG
    std::cout << "********\n";
    solver.print_assignment(std::cout);
    std::cout << "********\n";
#endif
    return false; // ok
  }

  if(passive_id >= num_threads)
  {
    const std::string opt="Spurious guard transitions requiring more than 1 passive thread";
    assert(stats.find(opt)!=stats.end());
    ++(stats[opt].val);
    return false; // can't do anything
  }

  print(9, "Guarded transition is spurious, refining");

  exprt condition;

  for(unsigned i=0; i < predicates.size(); ++i)
  {
    if(satcheck.is_in_conflict(predicate_variables_from[active_id][i]))
    {
      condition.operands().push_back(exprt());
      exprt &e=condition.operands().back();
      e=exprt(ID_predicate_symbol, bool_typet());
      e.set(ID_identifier, i);
      if(!from_predicates[active_id]->second[i]) e.make_not();
#ifdef DEBUG
      std::cout << "G-C: " << from_expr(concrete_model.ns, "", e) << std::endl;
#endif
    }

    if(passive_id!=active_id &&
        satcheck.is_in_conflict(predicate_variables_from[passive_id][i]))
    {
      condition.operands().push_back(exprt());
      exprt &e=condition.operands().back();
      e=exprt(ID_predicate_passive_symbol, bool_typet());
      e.set(ID_identifier, i);
      if(!from_predicates[passive_id]->second[i]) e.make_not();
#ifdef DEBUG
      std::cout << "G-C-F: " << from_expr(concrete_model.ns, "", e) << std::endl;
#endif
    }
  }

  gen_and(condition);

  if(c_instruction.is_goto())
  {  
    bool neg=abstract_state_from.branch_taken;
    constrain_goto_transition(abstract_transition_relation, condition, neg);
  }
  else
  {
    assert(c_instruction.is_assume());
    constrain_assume_transition(abstract_transition_relation, condition);
  }

  // spurious
  return true;
}

/*******************************************************************\

Function: transition_refinert::constrain_goto_transition

Inputs:

Outputs:

Purpose: add a constraint to a goto transition

\*******************************************************************/

void transition_refinert::constrain_goto_transition(
    abstract_transition_relationt &abstract_transition_relation,
    const exprt &condition,
    bool negated)
{
  if(abstract_transition_relation.constraints.size()==0)
  { 
    exprt schoose("bp_schoose", bool_typet());
    schoose.copy_to_operands(false_exprt(), false_exprt());
    abstract_transition_relation.constraints.push_back(schoose);
  }

  // we are only maintaining ONE constraint here
  assert(abstract_transition_relation.constraints.size()==1);

  exprt &schoose=
    abstract_transition_relation.constraints.front();

  exprt &constraint=negated?(schoose.op1()):(schoose.op0()); 

  if(constraint.is_false())
  {
    constraint.id(ID_or);
    constraint.copy_to_operands(false_exprt());
  }

  constraint.copy_to_operands(condition);
}

/*******************************************************************\

Function: transition_refinert::constrain_goto_transition

Inputs:

Outputs:

Purpose: add a constraint to an assume transition

\*******************************************************************/

void transition_refinert::constrain_assume_transition(
    abstract_transition_relationt &abstract_transition_relation,
    const exprt &condition)
{
  exprt negation=condition;
  negation.make_not();
  abstract_transition_relation.constraints.push_back(negation);
}

