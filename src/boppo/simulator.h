/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BOPPO_SIMULATOR_H
#define CPROVER_BOPPO_SIMULATOR_H

#include <hash_cont.h>

#include "simulator_base.h"
#include "history.h"
#include "queue.h"

class simulatort:public simulator_baset
{
public:
  simulatort(program_formulat &_program_formula):
    simulator_baset(_program_formula),
    enable_partial_order_reduction(false),
    enable_small_history(false),
    enable_qbf_cache(false),
    loops(false),
    mode(FULL),
    history(formula_container, _program_formula)
  {
  }
  
  virtual ~simulatort()
  {
  }
  
  void simulator();
  
  // options
  bool enable_partial_order_reduction;
  bool enable_small_history;
  bool enable_qbf_cache;
  bool loops;

  typedef enum { FULL, TVS } modet;
  modet mode;

protected:
  void run(queuet &queue);
  void explore(const statet &state, queuet &queue);

  void compute_successor_states(
    const statet &state,
    bool check_property,
    queuet &queue);
    
  // partial order reduction
  typedef std::list<unsigned> interleavingt;
  void compute_interleaving(const statet &state, interleavingt &interleaving);
  void partial_order_reduction(const statet &state, interleavingt &interleaving);
  bool is_local(
    const program_formulat::formula_goto_programt::instructiont
    &instruction);

  void compute_rw_sets(
    const program_formulat::formula_goto_programt::instructiont
    &instruction,
    std::set<unsigned> &read,
    std::set<unsigned> &write);
    
  void synchronization(
    const statet &state,
    queuet &queue);

  void compute_goto_successors(
    const statet &state,
    unsigned thread_nr,
    queuet &queue);

  void compute_start_thread_successors(
    const statet &state,
    unsigned thread_nr,
    queuet &queue);

  void compute_end_thread_successors(
    const statet &state,
    unsigned thread_nr,
    queuet &queue);

  void execute_thread(
    const statet &state,
    unsigned thread_nr,
    bool check_property,
    queuet &queue);
    
  void execute_instruction(
    statet &state,
    unsigned thread_nr,
    const program_formulat::formula_goto_programt::instructiont &instruction,
    bool check_property);

  void execute_assume(
    statet &state,
    unsigned thread_nr,
    const program_formulat::formula_goto_programt::instructiont &instruction);

  void execute_assert(
    statet &state,
    unsigned thread_nr,
    const program_formulat::formula_goto_programt::instructiont &instruction);

  void execute_assign(
    statet &state,
    unsigned thread_nr,
    const program_formulat::formula_goto_programt::instructiont &instruction);

  void execute_synchronize(
    statet &state,
    unsigned thread_nr,
    const program_formulat::formula_goto_programt::instructiont &instruction);

  void loop_detection(tracet &trace);

  // fixed point
  historyt history;
};

#endif
