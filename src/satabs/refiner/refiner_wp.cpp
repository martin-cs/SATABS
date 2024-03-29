/*******************************************************************\

Module: Predicate Refinement for CEGAR

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#include <cassert>
#include <iostream>
#include <sstream>

#include <util/expr_util.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/i2string.h>
#include <util/simplify_expr.h>

#include <goto-programs/wp.h>
#include <goto-symex/goto_symex_state.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include "../abstractor/predabs_aux.h"
#include "../abstractor/predicates.h"
#include "../prepare/concrete_model.h"

#include "refiner_wp.h"

#define DEBUG

/*******************************************************************\

Function: refiner_wpt::refine_prefix

Inputs:

Outputs:

Purpose: generate a new set of predicates given
a spurious counterexample

\*******************************************************************/

bool refiner_wpt::refine_prefix(
  predicatest &predicates, 
  abstract_modelt &abstract_model,
  const fail_infot &fail_info)
{
  status() << "Refining set of predicates according to counterexample (WP)" << eom;

  reset_num_predicates_added();

  bool found_new=false;

  // keep track of the loops that we're in (may be nested)
  std::list<fail_infot::induction_infot> loops;
  exprt invariant;
  if(fail_info.use_invariants)
    status() << "Using recurrence predicates detected by loop detection." << eom;

  debug() << "Inconsistent prefix:\n";

  for(abstract_counterexamplet::stepst::const_reverse_iterator 
      r_it=fail_info.steps.rbegin();
      r_it!=fail_info.steps.rend();
      r_it++)
  {
    abstract_programt::targett abstract_pc=r_it->pc;

    goto_programt::const_targett concrete_pc=
      abstract_pc->code.concrete_pc;

    if(concrete_pc->is_goto())
      debug() << "GUARD: " << (r_it->branch_taken?"(":"!(")
              << from_expr(concrete_model->ns, "", concrete_pc->guard) << ")";
    else if(concrete_pc->is_assert())
      debug() << "ASSERT: "
              << from_expr(concrete_model->ns, "", concrete_pc->guard);
    else if(concrete_pc->is_location())
      debug() << "LOC" << "\n";
    else if(concrete_pc->is_other() || concrete_pc->is_assign() || concrete_pc->is_decl())
      debug() << from_expr(concrete_model->ns, "", concrete_pc->code);
    else
    {
      debug() << concrete_pc->type;
    }

    debug() << "  // " << (concrete_pc->source_location);

    debug() << "\n" << "**********\n";
  }
  
  debug() << eom;


  {
    // get the constraint causing the failure

    exprt predicate=fail_info.guard;

#ifdef DEBUG
    std::cout << "P start0: " 
              << from_expr(concrete_model->ns, "", predicate) << std::endl;
#endif

    simplify(predicate, concrete_model->ns);

    abstract_counterexamplet::stepst::const_iterator 
      it=--fail_info.steps.end();

    // there must be at least two steps, or it's odd
    assert(it!=fail_info.steps.begin());

    {
      abstract_programt::targett abstract_pc=it->pc;

#ifdef DEBUG
      std::cout << "P start1: " 
                << from_expr(concrete_model->ns, "", predicate) << std::endl;
#endif

      add_predicates(
          abstract_pc, predicates, predicate, found_new, FROM);
    }

    // now do the WPs
    goto_symex_statet renaming_state;
    renaming_state.source.thread_nr=it->thread_nr;
    renaming_state.rename(predicate, concrete_model->ns, goto_symex_statet::L0);

    for(it--; // skip last instruction
        it!=fail_info.steps.begin();
        it--)
    {
#ifdef DEBUG
      std::cout << "refiner_wpt::refine_prefix_async 2\n";
#endif

      // handle loops 
      if(fail_info.use_invariants)
      {
        if(it->is_loop_begin())
        {
          loops.pop_back(); // pop induction_info if we leave loop

#ifdef DEBUG
          std::cout << "INV: "
                    << from_expr(concrete_model->ns, "", invariant) << std::endl;
#endif           

          exprt wp(ID_and, typet(ID_bool));
          wp.operands().resize(2);
          wp.op0().swap(invariant);
          wp.op1().swap(predicate);
          predicate.swap(wp);
        }
        else if(it->is_loop_end())
        {
          push_induction_info(fail_info, it, loops);
          invariant=true_exprt();
        }
      }

      if(!it->is_state())
        continue;

      if(predicate.is_false() && found_new)
      {
        // ok, refuted it, done
        break;
      }

      // add the predicate

      goto_programt::const_targett concrete_pc=
        it->pc->code.concrete_pc;

      abstract_programt::targett abstract_pc=it->pc;

#ifdef DEBUG
      std::cout << from_expr(concrete_model->ns, "", predicate) << std::endl;
#endif

      exprt no_tid_predicate=predicate;
      renaming_state.get_original_name(no_tid_predicate);
      add_predicates(abstract_pc, predicates, no_tid_predicate, found_new, TO);

      // skip irrelevant instructions
      if(!it->relevant) continue;

      exprt pred_bak=predicate;
      
#ifdef DEBUG
      goto_programt tmp;
      tmp.output_instruction(concrete_model->ns, "", std::cerr, concrete_pc);
#endif

      // compute weakest precondition
      switch(it->pc->type)
      {
        case ASSUME:
          // we only do this for assumptions
          // if we haven't found a new predicate so far
          if(1/*!found_new*/)
          {
            exprt tid_guard=concrete_pc->guard;
            renaming_state.source.thread_nr=it->thread_nr;
            renaming_state.rename(tid_guard, concrete_model->ns, goto_symex_statet::L0);
            predicate=and_exprt(tid_guard, predicate);
            simplify(predicate, concrete_model->ns);
          }
          break;

        case GOTO:
#ifdef DEBUG
          std::cout << "GOTO " << (it->branch_taken?"taken":"not taken") << "\n";
#endif
          {
            exprt tid_guard=concrete_pc->guard;
            if(!it->branch_taken) tid_guard.make_not();
            renaming_state.source.thread_nr=it->thread_nr;
            renaming_state.rename(tid_guard, concrete_model->ns, goto_symex_statet::L0);
            predicate=and_exprt(tid_guard, predicate);
            simplify(predicate, concrete_model->ns);
          }
          break;

        case OTHER:
        case DECL:
        case ASSIGN:
#ifdef DEBUG
          std::cout << "OTHER/ASSIGN/DECL\n";
#endif
          /* Ignore if user-specified predicate, otherwise treat like assign */
          if(it->pc->code.concrete_pc->code.get_statement()==ID_user_specified_predicate ||
             it->pc->code.concrete_pc->code.get_statement()==ID_user_specified_parameter_predicates ||
             it->pc->code.concrete_pc->code.get_statement()==ID_user_specified_return_predicates)
            break;

          {
            codet tid_tmp_code;
            if(!fail_info.use_invariants ||
                !get_instruction(concrete_pc, loops, tid_tmp_code, invariant))
              tid_tmp_code=to_code(concrete_pc->code);

#ifdef DEBUG
            std::cout << "A P before: " << from_expr(concrete_model->ns, "", predicate) << std::endl;
            std::cout << "Code:     " << from_expr(concrete_model->ns, "", tid_tmp_code) << std::endl;
#endif

            // compute weakest precondition
            if(tid_tmp_code.get_statement()==ID_assign)
              approximate_nondet(to_code_assign(tid_tmp_code).rhs());
            renaming_state.source.thread_nr=it->thread_nr;
            renaming_state.rename(tid_tmp_code, concrete_model->ns, goto_symex_statet::L0);
            exprt predicate_wp=wp(tid_tmp_code, predicate, concrete_model->ns);

            simplify(predicate_wp, concrete_model->ns);
            predicate=predicate_wp;

#ifdef DEBUG
            std::cout << "A P after:  " << from_expr(concrete_model->ns, "", predicate) << std::endl;
#endif
          }
          break;

        default:
          // ignore
          break;
      }

#ifdef DEBUG
      std::cout << "B P to-check:  " << from_expr(concrete_model->ns, "", predicate) << std::endl;
#endif

      if(pred_bak!=predicate)
      {
        satcheckt satcheck;
        bv_pointerst solver(concrete_model->ns, satcheck);
        solver.unbounded_array=boolbvt::U_NONE;
        literalt li=make_pos(concrete_model->ns, satcheck, solver, predicate);
        satcheck.set_assumptions(bvt(1, li));
        propt::resultt result=satcheck.prop_solve();
        assert(propt::P_SATISFIABLE==result || propt::P_UNSATISFIABLE==result);
        if(propt::P_UNSATISFIABLE==result)
          predicate=false_exprt();
        else
        {
          satcheck.set_assumptions(bvt(1, !li));
          propt::resultt result=satcheck.prop_solve();
          assert(propt::P_SATISFIABLE==result || propt::P_UNSATISFIABLE==result);
          if(propt::P_UNSATISFIABLE==result)
          {
            predicate=true_exprt();
            if(it->pc->type==ASSIGN)
            {
              const codet &code=concrete_pc->code;
              if(code.get_statement()==ID_assign)
              {
                equal_exprt pred_new(to_code_assign(code).lhs(),
                                     to_code_assign(code).rhs());
                simplify(pred_new, concrete_model->ns);
#ifdef DEBUG
                std::cout << "Adding new predicate as we arrived at TRUE: "
                  << from_expr(concrete_model->ns, "", pred_new) << std::endl;
#endif
                no_tid_predicate=pred_new;
                renaming_state.get_original_name(no_tid_predicate);
                add_predicates(abstract_pc, predicates, no_tid_predicate, found_new, FROM);
              }
            }
            else if(it->pc->type==ASSUME || it->pc->type==GOTO)
            {
              exprt pred_new=concrete_pc->guard;
              simplify(pred_new, concrete_model->ns);
#ifdef DEBUG
              std::cout << "Adding new predicate as we arrived at TRUE: "
                        << from_expr(concrete_model->ns, "", pred_new) << std::endl;
#endif
              no_tid_predicate=pred_new;
              renaming_state.get_original_name(no_tid_predicate);
              add_predicates(abstract_pc, predicates, no_tid_predicate, found_new, FROM);
            }
          }
        }
      }

#ifdef DEBUG
      std::cout << "B P after:   " << from_expr(concrete_model->ns, "", predicate) << std::endl;
#endif

      no_tid_predicate=predicate;
      renaming_state.get_original_name(no_tid_predicate);
      add_predicates(abstract_pc, predicates, no_tid_predicate, found_new, FROM);
    }

    if(!predicate.is_false() &&
       fail_info.warn_on_failure)
    {
      warning() << "Failed to refute spurious trace with WPs (got " <<
        from_expr(concrete_model->ns, "", predicate) << ")" << eom;
    }
  }

  if(found_new && fail_info.use_invariants)
  {
    add_induction_predicates(
        fail_info,
        abstract_model,
        predicates);
  }
  
  // make sure we have progress
  return !found_new;
}
