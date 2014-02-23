/*******************************************************************\

Module: Simulator based on Path-Symex

Author: Daniel Kroening

Date: January 2014

Purpose: Simulate an abstract counterexample on the concrete program
to determmine whether it is spurious.

\*******************************************************************/

#include <path-symex/build_goto_trace.h>

#include "../prepare/concrete_model.h"

#include "simulator_sat_dec.h"
#include "fail_info.h"
#include "concrete_counterexample.h"
#include "simulator_path_symex.h"

/*******************************************************************\

Function: simulator_path_symext::is_spurious

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool simulator_path_symext::is_spurious(
  const predicatest &predicates,
  const abstract_modelt &abstract_model,
  abstract_counterexamplet &abstract_counterexample,
  concrete_counterexamplet &concrete_counterexample,
  fail_infot &fail_info)
{
  status() << "Simulating abstract counterexample on concrete program" << eom;

  #if 0
  std::cout << "***********************************" << std::endl;
  std::cout << abstract_counterexample << std::endl;
  #endif

  if(path_slicing)
  {
    #if 0 // buggy right now
    status() << "Path slicing" << eom;
    path_slicer(
      ns,
      abstract_model.goto_functions,
      abstract_counterexample);
    #endif
  }

  #if 0
  std::cout << "***********************************" << std::endl;
  std::cout << abstract_counterexample << std::endl;
  std::cout << "***********************************" << std::endl;
  #endif

  // do symbolic simulation
  
  var_mapt var_map(concrete_model->ns);
  
  locst locs(concrete_model->ns);
  locs.build(concrete_model->goto_functions);
  path_symex_historyt path_symex_history;  
  
  path_symex_statet state=
    initial_state(var_map, locs, path_symex_history);
    
  target_to_loc_mapt target_to_loc_map(locs);

  do_path_symex(
    abstract_counterexample,
    target_to_loc_map,
    state);

  // run decision procedure

  status() << "Checking path of length "
           << state.get_depth() << eom;

  simulator_sat_dect satcheck(concrete_model->ns);
  
  if(!state.check_assertion(satcheck))
  {
    // the assertion fails, i.e., simulation succeeds
    build_goto_trace(state, satcheck, concrete_counterexample.goto_trace);
    status() << "Simulation successful" << eom;
    return false;
  }

  status() << "Spurious counterexample" << eom;

  // We now need to provide something useful for the refiner.

  fail_info.all_steps=abstract_counterexample.steps;
  fail_info.steps=abstract_counterexample.steps;
  
  fail_info.guard=
    not_exprt(abstract_counterexample.steps.back().pc->code.concrete_pc->guard);

  return true;
}

/*******************************************************************\

Function: simulator_path_symext::do_path_symex

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void simulator_path_symext::do_path_symex(
  const abstract_counterexamplet &abstract_counterexample,
  const target_to_loc_mapt &target_to_loc_map,  
  path_symex_statet &state)
{
  for(abstract_counterexamplet::stepst::const_iterator
      it=abstract_counterexample.steps.begin();
      it!=abstract_counterexample.steps.end();
      it++)
  {
    if(!it->is_state()) continue;

    bool last_state=abstract_counterexample.is_last_step(it);

    // get the concrete basic block
    goto_programt::const_targett c_target=it->pc->code.concrete_pc;

    // order of the below matters, as the PC is per-thread
    state.set_current_thread(it->thread_nr);
    state.set_pc(target_to_loc_map[c_target]);
    
    if(last_state)
    {
      if(!c_target->is_assert())
        throw "expected assertion at end of abstract trace";

      // we end when we are just about to execute the assertion
      break;
    }

    switch(c_target->type)
    {
    case GOTO:
      if(it->relevant)
        path_symex_goto(state, it->branch_taken);
      break;

    #if 0
    case ASSIGN:
      if(it->relevant)
      {
        bool passive_broadcast_only = false;
        for(goto_programt::instructiont::labelst::const_iterator
            l=c_target->labels.begin();
            !passive_broadcast_only && l!=c_target->labels.end();
            ++l)
          passive_broadcast_only = *l=="__CPROVER_passive_broadcast";

        for(unsigned t=0; t!=state.threads.size(); ++t)
        {
          if(passive_broadcast_only && t==it->thread_nr)
            continue;
          else if(!passive_broadcast_only && t!=it->thread_nr)
            continue;

          state.source.pc=c_target;
          state.source.thread_nr=t;
          symex_simulator.symex_step(concrete_model->goto_functions, state);
        }
  
        state.source.thread_nr=it->thread_nr;
      }
      break;
    #endif

    default:
      if(it->relevant)
        path_symex(state);
    }
  }
}


