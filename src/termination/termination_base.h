/*******************************************************************\

Module: Termination base class

Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_TERMINATION_BASE_H_
#define _CPROVER_TERMINATION_BASE_H_

#include <cmdline.h>
#include <ui_message.h>
#include <replace_expr.h>
#include <find_symbols.h>
#include <time_stopping.h>
#include <options.h>

#include <goto-symex/goto_trace.h>

#include <satabs/prepare/concrete_model.h>

#include "ranking_body.h"
#include "termination_results.h"

class contextt;
class goto_functionst;
class value_set_analysist;
class invariant_propagation;

extern const std::string termination_prefix;

class termination_baset:public messaget
{
public:
  termination_baset(const cmdlinet &_cmd,
                    const goto_functionst &_gf,
                    const contextt &_ctxt,
                    class contextt &_sctxt,
                    class value_set_analysist &_vsa,
                    class invariant_propagationt &_ip,
                    message_handlert &_mh,
                    ui_message_handlert::uit _ui);

  virtual termination_resultt operator()()=0;  

protected:
  const contextt &context;
  contextt &shadow_context;  
  const cmdlinet &cmdline;
  namespacet ns;
  ui_message_handlert::uit ui;
  optionst options;
  
  const goto_functionst &goto_functions;
  value_set_analysist &value_set_analysis;
  invariant_propagationt &invariant_propagation;
  
public:
  /* Prediacte abstraction options. */
  std::vector<exprt> user_provided_predicates;
  unsigned max_iterations;
  
  // some statistics
  fine_timet start_time;  
  fine_timet ranking_time;
  fine_timet modelchecker_time;
  fine_timet counter_example_extraction_time;
  fine_timet final_check_time;
  
  unsigned ranksynth_calls;
  unsigned total_loops;
  unsigned nonterminating_loops;
  
  virtual void show_stats(void);
  
protected:
  std::list<goto_programt::const_targett> last_path;  
  unsigned nondet_counter;

  goto_programt::const_targett find_next_loop(
    goto_programt::const_targett current,
    const goto_programt &program,
    std::list<goto_programt::const_targett> &recursion_stack) const;
  
  bodyt get_body(
    goto_tracet::stepst::const_iterator &loop_begin,
    const goto_tracet &trace);
  
  void adjust_assertion(const exprt &expr, goto_tracet &trace);
  goto_tracet::stepst::const_iterator get_loop(goto_tracet &trace);
  
  typedef std::set<const goto_trace_stept *> required_stepst;
  
  void find_required_steps(
    const goto_tracet &goto_trace,
    goto_tracet::stepst::const_iterator &loop_begin,
    required_stepst &required_steps,
    const std::string &prefix) const;

  static replace_mapt reverse_map(const replace_mapt &m)
  {
    replace_mapt result;

    for(replace_mapt::const_iterator it=m.begin();
        it!=m.end();
        it++)
    result[it->second]=it->first;

    return result;
  }
  
  bool intersects(
    const find_symbols_sett &a,
    const find_symbols_sett &b) const;
  
  void show_loop_trace(
    const goto_tracet &goto_trace,
    goto_tracet::stepst::const_iterator &loop_begin);
  
  void remove_ssa_ids(exprt &expr) const;
  
  void replace_nondet_sideeffects(exprt &expr);
  
  bool cegar(
    concrete_modelt &model,
    goto_tracet &goto_trace,
    fine_timet &modelchecker_time,
    fine_timet &unsafe_time,
    fine_timet &safe_time);
  
  bool cegar(
    concrete_modelt &model,
    fine_timet &modelchecker_time,
    fine_timet &unsafe_time,
    fine_timet &safe_time);
  
  bool bmc(
    concrete_modelt &model,  
    fine_timet &modelchecker_time,
    fine_timet &unsafe_time,
    fine_timet &safe_time);

  void set_options();
};

#endif
