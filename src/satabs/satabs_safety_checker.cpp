/*******************************************************************\

Module: Safety Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>
#include <fstream>

#include "abstractor/initial_abstraction.h"
#include "modelchecker/modelchecker_boolean_program.h"
#include "satabs_safety_checker.h"
#include "abstractor/abstractor.h"
#include "abstractor/select_abstractor.h"
#include "modelchecker/modelchecker.h"
#include "modelchecker/select_modelchecker.h"
#include "refiner/refiner.h"
#include "refiner/select_refiner.h"
#include "simulator/simulator.h"
#include "simulator/select_simulator.h"
#include "simulator/fail_info.h"
#include "prepare/concrete_model.h"
#include "simulator/concrete_counterexample.h"

/*******************************************************************\

Function: satabs_safety_checker_baset::satabs_safety_checker_baset

Inputs:

Outputs:

Purpose:

\*******************************************************************/

satabs_safety_checker_baset::satabs_safety_checker_baset(
    const namespacet &_ns,
    abstractort &_abstractor,
    refinert &_refiner,
    modelcheckert &_modelchecker,
    simulatort &_simulator):
  safety_checkert(_ns),
  max_iterations(0),
  save_bps(false),
  build_tts(false),
  concurrency_aware(false),
  write_csv_stats(false),
  abstractor(_abstractor),
  refiner(_refiner),
  modelchecker(_modelchecker),
  simulator(_simulator)
{
}

/*******************************************************************\

Function: satabs_safety_checker_baset::show_loop_component_statistics

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void satabs_safety_checker_baset::show_loop_component_statistics(
    const loop_componentt &lc,
    const std::string &name)
{
  std::ostringstream str;
  lc.statistics(str);
  if(!str.str().empty())
  {
    status() << "Statistics of " << name << ":" << eom;
    status(str.str());
  }
}

/*******************************************************************\

Function: satabs_safety_checker_baset::show_statistics

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void satabs_safety_checker_baset::show_statistics(const namespacet &ns)
{
  status() << "Time: "
           << total_time << " total, "
           << abstractor_time << " abstractor, "
           << modelchecker_time << " model checker, "
           << simulator_time << " simulator, "
           << refiner_time << " refiner"
           << eom;

  status() << "Number of iterations: " << iteration << eom;

  status() << "Number of predicates: " << predicates.size() << eom;

  for(unsigned p=0; p<predicates.size(); p++)
  {
    debug() << "P" << p << ": "
            << from_expr(ns, "", predicates[p])
            << eom;
  }

  if(concurrency_aware)
  {
    unsigned int local_count = 0;
    unsigned int shared_count = 0;
    unsigned int mixed_count = 0;

    for(unsigned int i = 0; i < predicates.size(); i++)
    {
      switch(abstractort::get_var_class(predicates[i], ns))
      {
        case abstract_modelt::variablet::THREAD_LOCAL:
        case abstract_modelt::variablet::PROCEDURE_LOCAL:
          local_count++;
          break;
        case abstract_modelt::variablet::SHARED_GLOBAL:
          shared_count++;
          break;
        case abstract_modelt::variablet::MIXED:
          mixed_count++;
          break;
        case abstract_modelt::variablet::NONE:
          assert(false);
      }
    }

    status() << "Breakdown of predicate types:" << endl
             << "   shared: " << shared_count << endl
             << "   local: " << local_count << endl
             << "   mixed: " << mixed_count << eom;
  }

  show_loop_component_statistics(abstractor, "abstractor");
  show_loop_component_statistics(modelchecker, "model checker");
  show_loop_component_statistics(simulator, "simulator");
  show_loop_component_statistics(refiner, "refiner");
}

/*******************************************************************\

Function: satabs_safety_checker_baset::csv_stats

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void satabs_safety_checker_baset::csv_stats(
    std::ofstream &of,
    const namespacet &ns)
{
  if(!write_csv_stats) return;

  assert(iteration>=1);
  assert(of.is_open());

  typedef std::list<std::pair<
    loop_componentt::statst::const_iterator, float> >
    loop_component_statst;
  static loop_component_statst lc_stats;

  if(iteration==1)
  {
    of << "iteration,\"nr predicates\",";
    if(concurrency_aware)
      of << "shared,mixed,local,";
    of << "\"total time\",";
    of << "\"abstractor time\",";
    of << "\"model checker time\",";
    of << "\"simulator time\",";
    of << "\"refiner time\",";

    std::list<loop_componentt const*> lcs;
    lcs.push_back(&abstractor);
    lcs.push_back(&modelchecker);
    lcs.push_back(&simulator);
    lcs.push_back(&refiner);
    for(std::list<loop_componentt const*>::const_iterator
        it=lcs.begin();
        it!=lcs.end();
        ++it)
      for(loop_componentt::statst::const_iterator
          it2=(*it)->stats.begin();
          it2!=(*it)->stats.end();
          ++it2)
        if(!it2->second.is_max)
        {
          lc_stats.push_back(std::make_pair(it2, 0));
          of << "\"" << it2->first << "\",";
        }
    of << std::endl;
  }

  of << iteration << "," <<
    predicates.size() << ",";

  if(concurrency_aware)
  {
    unsigned int local_count = 0;
    unsigned int shared_count = 0;
    unsigned int mixed_count = 0;

    for(unsigned int i = 0; i < predicates.size(); i++)
    {
      switch(abstractort::get_var_class(predicates[i], ns))
      {
        case abstract_modelt::variablet::THREAD_LOCAL:
        case abstract_modelt::variablet::PROCEDURE_LOCAL:
          local_count++;
          break;
        case abstract_modelt::variablet::SHARED_GLOBAL:
          shared_count++;
          break;
        case abstract_modelt::variablet::MIXED:
          mixed_count++;
          break;
        case abstract_modelt::variablet::NONE:
          assert(false);
      }
    }

    of << shared_count << ","
       << mixed_count << ","
       << local_count << ",";
  }

  {
    static fine_timet prev_tot_time=total_start_time;
    of << (current_time()-prev_tot_time);
    prev_tot_time=current_time();
    of << ",";
    static fine_timet prev_abs_time;
    of << (abstractor_time-prev_abs_time);
    prev_abs_time=abstractor_time;
    of << ",";
    static fine_timet prev_mc_time;
    of << (modelchecker_time-prev_mc_time);
    prev_mc_time=modelchecker_time;
    of << ",";
    static fine_timet prev_sim_time;
    of << (simulator_time-prev_sim_time);
    prev_sim_time=simulator_time;
    of << ",";
    static fine_timet prev_ref_time;
    of << (refiner_time-prev_ref_time);
    prev_ref_time=refiner_time;
    of << ",";
  }

  for(loop_component_statst::iterator
      it=lc_stats.begin();
      it!=lc_stats.end();
      ++it)
  {
    of << (it->first->second.val - it->second) << ",";
    it->second=it->first->second.val;
  }

  of << std::endl;
}

/*******************************************************************\

Function: satabs_safety_checker_baset::do_abstraction

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void satabs_safety_checker_baset::do_abstraction()
{
  fine_timet start_time=current_time();

  abstractor.build_abstraction(predicates);

  abstractor_time+=current_time()-start_time;
}

/*******************************************************************\

Function: satabs_safety_checker_baset::do_modelchecking

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool satabs_safety_checker_baset::do_modelchecking(
    const concrete_modelt &concrete_model,
    abstract_counterexamplet &abstract_counterexample)
{
  // do we want to save Boolean programs?
  if(save_bps)
  {
    modelchecker_boolean_programt model_checker_boolean_program(
        modelchecker_boolean_programt::BOPPO, 0, concurrency_aware,
        build_tts);
    model_checker_boolean_program.set_message_handler(get_message_handler());
    model_checker_boolean_program.save(
        abstractor.abstract_model,
        iteration);
  }

  fine_timet start_time=current_time();

  bool pass=
    modelchecker.check(abstractor.abstract_model,
        abstract_counterexample); 

  modelchecker_time+=current_time()-start_time;

  return pass;
}

/*******************************************************************\

Function: satabs_safety_checker_baset::do_simulation

Inputs:

Outputs:

Purpose:

\*******************************************************************/

bool satabs_safety_checker_baset::do_simulation(
    abstract_counterexamplet &abstract_counterexample,
    concrete_counterexamplet &concrete_counterexample,
    fail_infot &fail_info)
{
  fine_timet start_time=current_time();

  // Check the counterexample
  bool is_spurious=simulator.is_spurious(
      predicates,
      abstractor.abstract_model,
      abstract_counterexample,
      concrete_counterexample,
      fail_info);

  simulator_time+=current_time()-start_time;

  return is_spurious;
}

/*******************************************************************\

Function: satabs_safety_checker_baset::do_refinement

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void satabs_safety_checker_baset::do_refinement(
    const abstract_counterexamplet &abstract_counterexample,
    fail_infot &fail_info)
{
  fine_timet start_time=current_time();

  refiner.refine(
      predicates,
      abstractor.abstract_model,
      fail_info);

  refiner_time+=current_time()-start_time;
}

/*******************************************************************\

Function: satabs_safety_checker_baset::operator()

Inputs:

Outputs:

Purpose: execute the CEGAR loop

\*******************************************************************/

safety_checkert::resultt satabs_safety_checker_baset::operator()(
  const goto_functionst &goto_functions)
{
  status() << "*** Starting CEGAR Loop ***" << eom;
  
  resultt result=ERROR;
  total_start_time=current_time();
  iteration=0;

  concrete_modelt concrete_model(ns, goto_functions);

  // pass concrete model to all components
  abstractor.set_concrete_model(concrete_model);
  refiner.set_concrete_model(concrete_model);
  modelchecker.set_concrete_model(concrete_model);
  simulator.set_concrete_model(concrete_model);
  
  // pass message handler to all components

  abstractor.set_message_handler(get_message_handler());
  refiner.set_message_handler(get_message_handler());
  modelchecker.set_message_handler(get_message_handler());
  simulator.set_message_handler(get_message_handler());

  refiner.set_verbosity(get_verbosity());
  abstractor.set_verbosity(get_verbosity());
  modelchecker.set_verbosity(get_verbosity());
  simulator.set_verbosity(get_verbosity());    

  {
    // Create initial abstraction

    initial_abstractiont initial_abstraction(get_message_handler(),
        refiner.get_no_mixed_predicates());
    initial_abstraction.set_verbosity(get_verbosity());

    initial_abstraction.build(concrete_model, abstractor.abstract_model, concurrency_aware);

    if(initial_predicates.empty())
      initial_abstraction.init_preds(ns, predicates, concrete_model);
    else
      initial_abstraction.init_preds(
          ns, predicates, initial_predicates, abstractor.abstract_model);
  }

  std::auto_ptr<std::ofstream> csv(write_csv_stats?
      new std::ofstream("cegar.csv"):0);

  while(true) 
  {
    iteration++;

    status() << "*** CEGAR Loop Iteration " << iteration << eom;

    do_abstraction();

    // abstract counterexample 
    abstract_counterexamplet abstract_counterexample;

    // does the spec hold? 
    if(do_modelchecking(concrete_model, abstract_counterexample))
    {
      result=SAFE;
      break;
    }
    else
    { 
      fail_infot fail_info;
      concrete_counterexamplet concrete_counterexample;

      // Check the counterexample
      if(do_simulation(
            abstract_counterexample,
            concrete_counterexample,
            fail_info))
      {
        status() << "Trace is spurious" << eom;

        if(iteration==max_iterations)
        {
          error() << "Too many iterations, giving up." << eom;
          error() << "Consider increasing the number of iterations." << eom;
          result=ERROR;
          break;
        }

        // it is spurious, refine
        do_refinement(abstract_counterexample, fail_info);
      }
      else
      {
        // counterexample is not spurious -- store it
        // as error trace
        error_trace.swap(concrete_counterexample.goto_trace);
        result=UNSAFE;
        break;
      }
    }

    csv_stats(*csv, concrete_model.ns);
  }

  total_time=current_time()-total_start_time;
  show_statistics(concrete_model.ns);
  csv_stats(*csv, concrete_model.ns);

  return result;
}

/*******************************************************************\

Function: satabs_safety_checker_baset::re_abstract

Inputs:

Outputs:

Purpose: mark an instruction for re-abstraction

\*******************************************************************/

void satabs_safety_checker_baset::re_abstract(const goto_programt::const_targett target)
{
  abstract_functionst &afuncs=abstractor.abstract_model.goto_functions;
  for(abstract_functionst::function_mapt::iterator it=
      afuncs.function_map.begin();
      it!=afuncs.function_map.end();
      it++)
  {
    for(abstract_programt::instructionst::iterator iit=
        it->second.body.instructions.begin();
        iit!=it->second.body.instructions.end();
        iit++)    
    {
      if(iit->code.concrete_pc==target)
      {
        iit->code.re_abstract=true;
        return;
      }
    }
  }
}  

/*******************************************************************\

Function: satabs_componentst::satabs_componentst

Inputs:

Outputs:

Purpose:

\*******************************************************************/

satabs_componentst::satabs_componentst(
  const optionst &options,
  symbol_tablet &_shadow_symbol_table):
  abstractor_ptr(select_abstractor(options)),
  refiner_ptr(select_refiner(options)),
  modelchecker_ptr(select_modelchecker(options)),
  simulator_ptr(select_simulator(options, _shadow_symbol_table))
{
}

/*******************************************************************\

Function: satabs_safety_checkert::satabs_safety_checkert

Inputs:

Outputs:

Purpose:

\*******************************************************************/

satabs_safety_checkert::satabs_safety_checkert(
  const symbol_tablet &_symbol_table,
  const optionst &options):
  satabs_componentst(options, shadow_symbol_table),
  satabs_safety_checker_baset(
    ns, *abstractor_ptr, *refiner_ptr, *modelchecker_ptr, *simulator_ptr),
  ns(_symbol_table, shadow_symbol_table)
{
  max_iterations=options.get_int_option("iterations");
}
