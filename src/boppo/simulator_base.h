/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BOPPO_SIMULATOR_BASE_H
#define CPROVER_BOPPO_SIMULATOR_BASE_H

#include "program_formula.h"
#include "state.h"
#include "trace.h"

class simulator_baset
{
public:
  simulator_baset(program_formulat &_program_formula):
    slam(false),
    compact_trace(false),
    program_formula(_program_formula)
  {
  }
  
  virtual ~simulator_baset()
  {
  }
  
  virtual void simulator()=0;
  
  // result
  bool error_state_found;

  // interface
  bool slam;
  bool slam_race;
  bool compact_trace;
  std::string slam_file;
  
protected:
  program_formulat &program_formula;
  formula_containert formula_container;

  typedef program_formulat::formula_goto_programt::targett targett;
  typedef program_formulat::formula_goto_programt::const_targett const_targett;
  typedef program_formulat::formula_goto_programt::instructiont instructiont;

  typedef std::vector<const_targett> PCst;
  typedef std::vector<formulat> valuest;
  
  statet make_initial_state();

  formulat instantiate(
    const statet &state,
    unsigned t,
    formulat formula)
  {
    return instantiate(state.data(), NULL, t, formula);
  }
  
  formulat instantiate(
    const state_dt &current,
    const state_dt *next,
    unsigned t,
    formulat formula);

  formulat instantiate(
    const statet &current,
    const statet &next,
    unsigned t,
    formulat formula)
  {
    return instantiate(current.data(), &next.data(), t, formula);
  }

  void dump_trace(
    tracet &trace, 
    const program_formulat::formula_goto_programt::instructiont &instruction);

  void dump_full_trace(tracet &trace);
  void dump_compact_trace(tracet &trace);

  void compute_trace(
    const statet &state,
    tracet &trace,
    bool assertion);

  // solver
  bool is_satisfiable(formulat formula);
  bool is_satisfiable(class cnf_solvert &solver);
};

#endif
