/*******************************************************************\

Module: Symbolic Simulator (Path Pretty Printer for SLAM)

Author: Daniel Kroening, kroening@kroening.com
        Georg Weissenbacher, georg.weissenbacher@inf.ethz.ch

\*******************************************************************/

#ifndef CPROVER_BOPPO_SLAM_TRACE_H
#define CPROVER_BOPPO_SLAM_TRACEH

#include <stack>

#include "simulator.h"

class slam_predicatest
{
public:
  typedef std::map<std::string, std::string> predicate_mapt;
 
  void read(const std::string &file);
  slam_predicatest();
  slam_predicatest(const std::string &file);
  std::string operator[](const std::string &id) const;

protected:
  predicate_mapt predicate_map;  
};

/* serves to store the state information of a concurrent trace */
class trace_infot
{
public:
  trace_infot (unsigned _thread_id, 
	       unsigned _block,
	       unsigned _instruction,
	       const std::string &_pre_globals,
	       const std::string &_pre_locals,
	       const std::string &_fname):
    thread_id (_thread_id),
    block (_block),
    instruction (_instruction),
    pre_globals (_pre_globals),
    pre_locals (_pre_locals),
    function_name (_fname)
    {
      next_block = -1;
      next_instruction = -1;
      call_return_block = 0;
      is_return_stmt = false;
      slic_error = false;
      is_calling_stmt = false;
    }
  
  unsigned thread_id;
  unsigned block;
  unsigned instruction;
  int next_block;
  int next_instruction;
  unsigned call_return_block;
  bool is_calling_stmt;
  bool is_return_stmt;
  bool slic_error;

  std::string pre_globals;
  std::string pre_locals;
  std::string post_globals;
  std::string post_locals;
  std::string function_name;    
};

class slam_dumpt
{
public:
  typedef std::vector<std::vector<class trace_infot> > split_tracet;

  slam_dumpt (program_formulat &_program_formula, 
	      tracet &_trace,
	      const program_formulat::formula_goto_programt::instructiont &_instruction,
	      std::string &_slam_file):
    program_formula (_program_formula), 
    trace (_trace),
    last_instruction (_instruction),
    slam_file (_slam_file)
    {
      /* make sure that thread ids are not reused */
      //thread_num = slam_dumpt::adjust_thread_ids (trace);
      thread_num = number_of_threads (trace);
      current_thread = 0;
      previous_thread = 0;
    }

  void dump_trace_slam();
  void dump_concurrent_trace_slam();
  static unsigned adjust_thread_ids (tracet &trace);

protected:
  program_formulat &program_formula;
  tracet &trace;
  const program_formulat::formula_goto_programt::instructiont &last_instruction;

  std::string &slam_file;
  split_tracet splitted_trace;
  std::vector<unsigned> thread_step;
  std::vector<unsigned> current_blocks;
  std::vector<tracet::const_iterator> previous_thread_step;

  unsigned thread_num;
  unsigned current_thread;
  unsigned previous_thread;

  void split_trace (slam_predicatest& slam_predicates);
  void process_labels (const std::list<irep_idt> &labels,
		       const trace_stept &trace_step,
		       slam_predicatest& slam_predicates);
  void process_instr_label (const std::string &label,
			    const trace_stept& trace_step,
			    slam_predicatest& slam_predicates);

  const std::string get_global_state (const trace_stept &trace_step,
				const slam_predicatest &preds);
  const std::string get_local_state (const trace_stept &trace_step, 
				     const slam_predicatest &preds,
				     unsigned thread_id);
  unsigned number_of_threads (const tracet &trace);

  void write_trace_to_file (std::ofstream &file);
};


#endif
