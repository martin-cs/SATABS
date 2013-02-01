/*******************************************************************\

Module: Safety Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SATABS_SAFETY_CHECKER_H
#define CPROVER_SATABS_SAFETY_CHECKER_H

#include <time_stopping.h>
#include <options.h>

#include <goto-programs/safety_checker.h>

#include <langapi/language_ui.h>

#include "abstractor/predicates.h"
#include "prepare/concrete_model.h"
#include "loop_component.h"

class abstractort;
class refinert;
class modelcheckert;
class simulatort;
class abstract_counterexamplet;
class concrete_counterexamplet;
class concrete_modelt;
class fail_infot;
class loop_componentt;

class satabs_safety_checker_baset:public safety_checkert
{
public:
  // components given
  explicit satabs_safety_checker_baset(
    const namespacet &_ns,
    abstractort &abstractor,
    refinert &refiner,
    modelcheckert &modelchecker,
    simulatort &simulator);

  // you can add some predicates that are there right
  // from the beginning
  std::vector<exprt> initial_predicates;

  // ui
  language_uit::uit ui;

  // how many times to go through CEGAR
  unsigned max_iterations;

  // save the Boolean programs?
  bool save_bps;

  // build thread transition systems?
  bool build_tts;

  // handle concurrency using CAV'11 technique?
  bool concurrency_aware;

  // write statistics?
  bool write_csv_stats;

  virtual resultt operator()(
    const goto_functionst &goto_functions);

  void re_abstract(const goto_programt::const_targett target);

protected:
  // the four well-known components of the CEGAR loop
  abstractort &abstractor;
  refinert &refiner;
  modelcheckert &modelchecker;
  simulatort &simulator;

  // collecting statistics
  fine_timet total_time;
  fine_timet total_start_time;
  fine_timet abstractor_time;
  fine_timet modelchecker_time;
  fine_timet simulator_time;
  fine_timet refiner_time;

  void show_statistics(const namespacet &ns);

  // implementation

  unsigned iteration;
  predicatest predicates;

  void do_abstraction();

  void do_refinement(
      const abstract_counterexamplet &abstract_counterexample,
      class fail_infot &fail_info);

  bool do_modelchecking(
      const concrete_modelt &concrete_model,
      abstract_counterexamplet &abstract_counterexample);

  bool do_simulation(
      abstract_counterexamplet &abstract_counterexample,
      concrete_counterexamplet &concrete_counterexample,
      fail_infot &fail_info);

  void csv_stats(
      std::ofstream &of,
      const namespacet &ns);

  void show_loop_component_statistics(
      const loop_componentt &lc,
      const std::string &name);
};

class satabs_safety_checkert:public satabs_safety_checker_baset
{
public:
  // select components from options
  explicit satabs_safety_checkert(
    const namespacet &_ns,
    const goto_functionst &goto_functions,
    const optionst &options,
    contextt &shadow_context,
    message_handlert &message_handler);

protected:
  concrete_modelt concrete_model;
  loop_componentt::argst args;

  std::auto_ptr<abstractort> abstractor_ptr;
  std::auto_ptr<refinert> refiner_ptr;
  std::auto_ptr<modelcheckert> modelchecker_ptr;
  std::auto_ptr<simulatort> simulator_ptr;
};

#endif
