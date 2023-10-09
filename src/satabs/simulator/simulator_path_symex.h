/*******************************************************************\

Module: Simulator

Author: Daniel Kroening
    
Date: January 2014

Purpose: Simulate an abstract counterexample on the concrete program
to determmine whether it is spurious.

\*******************************************************************/

#ifndef CPROVER_SATABS_SIMULATOR_PATH_SYMEX_H
#define CPROVER_SATABS_SIMULATOR_PATH_SYMEX_H

#include <util/options.h>

#include <path-symex/path_symex.h>

#include "simulator.h"
#include "../modelchecker/abstract_counterexample.h"

class simulator_path_symext:public simulatort
{
public:
  simulator_path_symext(const optionst &options):
    path_slicing(!options.get_bool_option("no-path-slicing")),
    shortest_prefix(options.get_bool_option("shortest-prefix"))
  {
  }

  // Returns TRUE if the counterexample is spurious,
  // and FALSE otherwise. If FALSE is returned, a concrete
  // counterexample is provided as well

  virtual bool is_spurious(
    const predicatest &predicates,
    const abstract_modelt &abstract_model,
    abstract_counterexamplet &abstract_counterexample,
    concrete_counterexamplet &concrete_counterexample,
    fail_infot &fail_info);

  bool path_slicing;
  bool shortest_prefix;

protected:
  void do_path_symex(
    const abstract_counterexamplet &abstract_counterexample,
    const target_to_loc_mapt &target_to_loc_map,
    path_symex_statet &state);
};

#endif
