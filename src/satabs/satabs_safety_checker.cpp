/*******************************************************************\

Module: Safety Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>
#include <fstream>

#include <i2string.h>

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
    status("Statistics of "+name+":");
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
  {
    std::ostringstream str;
    str << "Time: ";
    output_time(total_time, str);
    str << " total, ";
    output_time(abstractor_time, str);
    str << " abstractor, ";
    output_time(modelchecker_time, str);
    str << " model checker, ";
    output_time(simulator_time, str);
    str << " simulator, ";
    output_time(refiner_time, str);
    str << " refiner";
    status(str.str());
  }

  {
    std::ostringstream str;
    str << "Iterations: " << iteration;
    status(str.str());
  }

  {
    std::ostringstream str;
    str << "Predicates: " << predicates.size();
    status(str.str());

    std::ostringstream str2;
    for(unsigned p=0; p<predicates.size(); p++)
    {
      str2 << "P" << p << ": "
        << from_expr(ns, "", predicates[p])
        << std::endl;
    }
    print(10, str2.str());

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
    std::ostringstream str;
    str << "Breakdown of predicate types:" << std::endl << "   shared: " << shared_count << std::endl << "   local: " << local_count << std::endl << "   mixed: " << mixed_count;
    status(str.str());
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
    output_time(current_time()-prev_tot_time, of);
    prev_tot_time=current_time();
    of << ",";
    static fine_timet prev_abs_time=0;
    output_time(abstractor_time-prev_abs_time, of);
    prev_abs_time=abstractor_time;
    of << ",";
    static fine_timet prev_mc_time=0;
    output_time(modelchecker_time-prev_mc_time, of);
    prev_mc_time=modelchecker_time;
    of << ",";
    static fine_timet prev_sim_time=0;
    output_time(simulator_time-prev_sim_time, of);
    prev_sim_time=simulator_time;
    of << ",";
    static fine_timet prev_ref_time=0;
    output_time(refiner_time-prev_ref_time, of);
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
        loop_componentt::argst(get_message_handler(), concrete_model),
        modelchecker_boolean_programt::BOPPO, 0, concurrency_aware,
        build_tts);
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
  status("*** Starting CEGAR Loop ***");

  resultt result=ERROR;
  total_start_time=current_time();
  abstractor_time=0;
  modelchecker_time=0;
  simulator_time=0;
  refiner_time=0;
  iteration=0;

  concrete_modelt concrete_model(ns, goto_functions);

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

    status("*** CEGAR Loop Iteration "+i2string(iteration));

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
        status("Trace is spurious");

        if(iteration==max_iterations)
        {
          error("Too many iterations, giving up.");
          error("Consider increasing the number of iterations.");
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

Function: satabs_safety_checker_baset::satabs_safety_checker_baset

Inputs:

Outputs:

Purpose:

\*******************************************************************/

#if 0
satabs_safety_checkert::satabs_safety_checkert(
  const namespacet &_ns,
  const goto_functionst &_goto_functions,
  const optionst &options,
  contextt &shadow_context,
  message_handlert &_message_handler):
  concrete_model(_ns, _goto_functions),
  args(_message_handler, concrete_model),
  abstractor_ptr(select_abstractor(options, args)),
  refiner_ptr(select_refiner(options, args)),
  modelchecker_ptr(select_modelchecker(options, args)),
  simulator_ptr(select_simulator(options, args, shadow_context)),
  satabs_safety_checker_baset(
    _ns, *abstractor_ptr, *refiner_ptr, *modelchecker_ptr, *simulator_ptr)
{
}
#endif
