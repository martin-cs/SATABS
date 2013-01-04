/*******************************************************************\

Module: Symbolic Simulator (Path Pretty Printer for SLAM)

Author: Daniel Kroening, kroening@kroening.com
        Georg Weissenbacher, georg.weissenbacher@inf.ethz.ch

\*******************************************************************/

#include <assert.h>
#include <string.h>

#include <fstream>
#include <sstream>

#include <prefix.h>

#include <algorithm>
#include <cstdlib>

#include <map>

#include "slam_trace.h"

/*******************************************************************\

   Class: slam_predicatest

 Purpose: stores the mapping from boolean variables to predicates

\*******************************************************************/

slam_predicatest::slam_predicatest() { }

/*******************************************************************\

Function: slam_predicatest::slam_predicatest

  Inputs: file name as string

 Outputs:

 Purpose: reads predicates from a file and maps them to variables

\*******************************************************************/
  
slam_predicatest::slam_predicatest(const std::string &file)
{
  read(file);
}
  
/*******************************************************************\

Function: slam_dumpt::slam_predicatest::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string slam_predicatest::operator[](const std::string &id) const
{
  slam_predicatest::predicate_mapt::const_iterator it=predicate_map.find(id);
  if(it==predicate_map.end()) return "";
  return it->second;
}

/*******************************************************************\

Function: slam_dumpt::slam_predicatest::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void slam_predicatest::read(const std::string &file)
{
  std::ifstream in(file.c_str());
  
  if(!in)
    throw "failed to open "+file;
    
  std::string line;
  while(std::getline(in, line))
  {
    std::string id=line;
    std::getline(in, line);
    predicate_map[id]=line;
    std::getline(in, line);
  }
}

/*******************************************************************\

Function: is_slam_label_L

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static bool is_slam_label_L(const std::string &label)
{
  // check if label == Lnnnn

  if(label=="") return false;
  
  if(label[0]!='L') return false;
  
  for(unsigned i=1; i<label.size(); i++)
    if(!isdigit(label[i])) return false;
  
  return true;
}

/*******************************************************************\

Function: is_c2bp_label

  Inputs: a string representing a label

 Outputs: true, if label is a c2bp label (c2bp...), else false 

 Purpose: 

\*******************************************************************/

bool is_c2bp_label (const std::string &label)
{
  const char* prefix = "c2bp";

  return (label.length () > strlen (prefix) && 
	  has_prefix(label, prefix));
}

/*******************************************************************\

Function: is_return_stmt_label

  Inputs: a string representing a label

 Outputs: true, if label is a c2bpreturnstmt... label, 
          else false 

 Purpose: 

\*******************************************************************/

bool is_return_stmt_label (const std::string &label)
{
  const char* prefix = "c2bpreturnstmt";

  return (label.length () > strlen (prefix) && 
	  has_prefix(label, prefix));
}

/*******************************************************************\

Function: is_call_rtb_label

  Inputs: a string representing a label

 Outputs: true, if label is a c2bpcallrtb... label, 
          else false 

 Purpose: 

\*******************************************************************/

bool is_call_rtb_label (const std::string &label)
{
  const char* prefix = "c2bpcallrtb_";

  return (label.length () > strlen (prefix) && 
	  has_prefix(label, prefix));
}

/*******************************************************************\

Function: is_calling_stmt_label

  Inputs: a string representing a label

 Outputs: true, if label is a c2bcall_... label, 
          else false 

 Purpose: 

\*******************************************************************/

bool is_calling_stmt_label (const std::string &label)
{
  const char* prefix = "c2bpcall_";

  return (label.length () > strlen (prefix) && 
	  has_prefix(label, prefix));
}

/*******************************************************************\

Function: is_block_label

  Inputs: a string representing a label

 Outputs: true, if label is a block label (c2bp_b_...), else false 

 Purpose: used to find a block label in a list of labels

\*******************************************************************/

bool is_block_label (const std::string &label)
{
  return (label.length () > 6 && 
	  is_c2bp_label (label) &&
	  label[5] == 'b');
}

/*******************************************************************\

Function: is_instruction_label

  Inputs: a string representing a label

 Outputs: true, if label is a block label (c2bp_b_...), else false 

 Purpose: used to find an instruction label in a list of labels

\*******************************************************************/

bool is_instruction_label (const std::string &label)
{
  return (label.length () > 6 && 
	  is_c2bp_label (label) && 
	  label[5] == 'i');
}

/*******************************************************************\

Function: is_error_label

  Inputs: a string representing a label

 Outputs: true, if label is an error label

 Purpose: used to find an error label in a list of labels

\*******************************************************************/

bool is_error_label (const std::string &label)
{
  return (label == "SLIC_ERROR");
}

/*******************************************************************\

Function: get_block_index

  Inputs: a type (either 'i' for instruction or 'b' for block), 
          and a label of form c2bp_x_n[_m], where x equals type

 Outputs: integer value of n (see Inputs)

 Purpose: Extract block numbers of Boolean program for SLAM

\*******************************************************************/

static unsigned get_block_index (const char type, const std::string &label)
{
  std::string::size_type start, end;
  unsigned result;

  switch (type) {
  case 'i': 
    assert (is_instruction_label (label));
    break;
  default:
    assert (is_block_label (label) ||
	    is_call_rtb_label (label));
  }

  if (is_instruction_label (label) || is_block_label (label))
    start = strlen ("c2bp_x_");
  else {
    assert (is_call_rtb_label (label));
    start = strlen ("c2bpcallrtb_");
  }

  end = label.find ('_', start);
  const std::string &index = label.substr (start, end-1);
  result = atoi (index.c_str());
  assert (result);
  return result;
}

/*******************************************************************\

Function: get_instruction_index

  Inputs: a label of form c2bp_i_n_m

 Outputs: integer value of m (see Inputs)

 Purpose: Extract instruction numbers of Boolean program for SLAM

\*******************************************************************/

static unsigned get_instruction_index (const std::string &label)
{
  std::string::size_type start;
  unsigned result;

  assert (is_instruction_label (label));

  start = label.find_last_of ('_');
  const std::string &index = label.substr (start+1);
  
  result = atoi (index.c_str());
  assert (result);
  return result;
}

/*******************************************************************\

Function: adjust_thread_ids

  Inputs: a trace

 Outputs: returns the number of threads in the trace

 Purpose: destructively updates the thread ids such that no
          thread ids are reused/recycled

\*******************************************************************/

unsigned slam_dumpt::adjust_thread_ids (tracet &trace)
{
  unsigned max_thread_id = 0;
  unsigned max_assigned_thread_id = 0;

  std::map<unsigned, unsigned> thread_map;

  /* initialize the thread id map */
  for(tracet::iterator t_it=trace.begin();
      t_it!=(tracet::iterator)trace.end();
      t_it++)
    {
      trace_stept &trace_step=*t_it;
      if (trace_step.is_initial_state) 
	continue;
      thread_map[trace_step.previous_thread] = trace_step.previous_thread;
      if (trace_step.previous_thread > max_thread_id)
	max_thread_id = trace_step.previous_thread;
    }

  /* now correct the thread ids such that no thread ids are reused */
  for(tracet::iterator t_it=trace.begin();
      t_it!=(tracet::iterator)trace.end();
      t_it++)
  {
    trace_stept &trace_step=*t_it;
    if (trace_step.is_initial_state)
      continue;

    trace_step.previous_thread = thread_map[trace_step.previous_thread];
    if (trace_step.previous_thread > max_assigned_thread_id)
      max_assigned_thread_id = trace_step.previous_thread;
    
    if (trace_step.previous_PC->type == END_THREAD)
      thread_map[trace_step.previous_thread] = ++max_thread_id;
  }
  
  return (max_assigned_thread_id + 1);
}

/*******************************************************************\

Function: slam_dumpt:dump_trace_slam

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void slam_dumpt::dump_trace_slam()
{
  // strip .bp
  assert(slam_file.size()>3);
  assert(std::string(slam_file, slam_file.size()-3, 3)==".bp");
  
  std::string base_file_name(slam_file, 0, slam_file.size()-3);

  std::string path_file_name=base_file_name+".p";
  std::string predicates_file_name=base_file_name+".v";
  
  slam_predicatest slam_predicates(predicates_file_name);

  std::ofstream slam_path_file(path_file_name.c_str());
  
  tracet::const_reverse_iterator p_it;
  
  for(tracet::const_reverse_iterator t_it=trace.rbegin();
      t_it!=(tracet::const_reverse_iterator)trace.rend();
      p_it=t_it, t_it++)
  {
    const trace_stept &trace_step=*t_it;

    if(t_it==(tracet::const_reverse_iterator)trace.rbegin())
    {
      slam_path_file << get_global_state (trace_step, slam_predicates);
      slam_path_file << get_local_state (trace_step, slam_predicates, 0);

      slam_path_file << ";" << std::endl;

      for(std::list<irep_idt>::const_iterator
          l_it=last_instruction.labels.begin();
	  l_it!=last_instruction.labels.end();
	  l_it++)
	{
	  if(has_prefix(id2string(*l_it), "c2bp_b_")) //"c2bp_stmt"))
	    {
	      slam_path_file << get_block_index ('b', id2string(*l_it)) << std::endl;
	  
	      slam_path_file 
		<< "// " << trace_step.previous_PC->location.get ("function") << std::endl;
	    }
	}
    }
    else
    {
      const trace_stept &previous_step=*p_it;
      
      assert(!previous_step.is_initial_state);

      const std::list<irep_idt> &labels=
	previous_step.previous_PC->labels;
 
      if(labels.empty())
        continue;
      
      /* SLAM is not interested in paths through malloc */
      const std::string &fname =
        trace_step.previous_PC->location.get_string("function");
        
      if (fname.find ("malloc_") != std::string::npos)
	continue;

      /* there might be more than one instruction shuffled into one state */
      /* and alas, exactly in the wrong order. So reverse this            */
      std::list<std::string> split;
      std::stack<std::list<std::string> > state_stack;

      for (std::list<irep_idt>::const_iterator 
           l_it = labels.begin ();
	   l_it != labels.end ();
	   l_it++)
	{
	  const std::string &label = id2string(*l_it);
	  if (is_block_label (label) || is_instruction_label (label))
	    split.push_back (label);
	  
	  if (is_block_label (label)       /* terminated by a block label */ 
	      || (label == (id2string(*labels.rbegin()))))          /* or end of list */
	    {
	      state_stack.push (split);
	      split.clear ();
	    }
	}
	  
      while (!state_stack.empty ())
	{
	  unsigned block_index = 0;

	  std::list<std::string> &current = state_stack.top ();

	  for(std::list<std::string>::const_iterator
		l_it=current.begin();
	      l_it!=current.end();
	      l_it++)
	    {
	      const std::string &label=*l_it;

	      if(is_instruction_label (label))
		{
		  /* output only global variables or active local variables */
		  slam_path_file << get_global_state (trace_step, slam_predicates);
		  slam_path_file << get_local_state (trace_step, slam_predicates, 0);
		  
		  slam_path_file << ";" << std::endl;

		  block_index = get_block_index ('i', label);
		}

	    }
	  
	  for(std::list<std::string>::const_iterator
		l_it=current.begin();
	      l_it!=current.end();
	      l_it++)
	    {
	      const std::string &label=*l_it;
	      
	      if(is_block_label (label))
		{
		  //assert (block_index == get_block_index ('b', label));
		  slam_path_file << block_index  << std::endl;
		  
		  // function name
		  
		  slam_path_file
		    << "// " << fname << std::endl;
		}
	    }

	  /* discard labels so we can proceed with the next state*/
	  state_stack.pop ();
	}
    }
  }
}

/*******************************************************************\

Function: get_global_state

  Inputs: trace step

 Outputs: the global state as a string

 Purpose:

\*******************************************************************/

const std::string 
slam_dumpt::get_global_state (const trace_stept &trace_step,
			     const slam_predicatest &preds)
{
  std::ostringstream result;
  
  for(unsigned v=0; v<program_formula.variables.size(); v++)
    {
      if (program_formula.variables[v].is_global)
	{
	  const std::string p=
	    preds[id2string(program_formula.variables[v].base_name)];
	  
	  if(p!="")
	    result << p << "=" << trace_step.global_values[v] << " ";
	}
    }
  
  return result.str ();
}

/*******************************************************************\

Function: get_local_state

  Inputs: trace step

 Outputs: the local state of a step as a string

 Purpose:

\*******************************************************************/

const std::string 
  slam_dumpt::get_local_state (const trace_stept &trace_step,
			       const slam_predicatest &preds,
			       unsigned thread_id)
{
  std::ostringstream result;
  unsigned no_globals = program_formula.no_globals;
  assert (trace_step.global_values.size() == no_globals);

  for(unsigned v=0; v<program_formula.no_locals; v++)
    {
      bool is_local = 
	(id2string(program_formula.variables[v+no_globals].identifier).find
	 (trace_step.previous_PC->location.get_string("function")) 
	 != std::string::npos);

      if (is_local)
	{
	  const std::string p=
	    preds[id2string(program_formula.variables[v+no_globals].base_name)];
	  
	  if(p!="")
	    result <<  p << "=" << 
	      trace_step.threads[thread_id].local_values[v] << " ";
	}
    }
      
  return result.str ();
}


/*******************************************************************\

Function: number of threads

  Inputs: trace

 Outputs: deprecated

 Purpose: deprecated. Don't use.

\*******************************************************************/

unsigned 
slam_dumpt::number_of_threads (const tracet &trace)
{
  /* find out the maximum number of threads */
  unsigned threads = 0;

  for(tracet::const_iterator t_it=trace.begin ();
     t_it != trace.end (); t_it++)
    if (t_it->threads.size() > threads)
      threads = t_it->threads.size();

  return threads;
}


/*******************************************************************\

Function: symbolic_simulatort::split_trace

  Inputs:

 Outputs: 

 Purpose: processes a trace and pushes the state information onto
          the stack that corresponds to the thread of the state

\*******************************************************************/

void slam_dumpt::split_trace(slam_predicatest& slam_predicates)
{
  assert (thread_num == splitted_trace.size () &&
	  thread_num == current_blocks.size ());

  for(tracet::const_iterator t_it=trace.begin();
      t_it!= trace.end();
      previous_thread = current_thread,
      previous_thread_step[previous_thread] = t_it, t_it++)
    {
      const trace_stept &trace_step = *t_it;

      /* there are no labels in the initial state */
      if (trace_step.is_initial_state)
	continue;

      current_thread = trace_step.previous_thread;

      const std::list<irep_idt> &labels=trace_step.previous_PC->labels;

      process_labels(labels, trace_step, slam_predicates);
    }
  
  /* we might need the following information when printing the path       */
  (splitted_trace[current_thread].back ()).slic_error = true;
}

/*******************************************************************\

Function: symbolic_simulatort::process_labels

  Inputs:

 Outputs: 

 Purpose: processes the labels of a trace_step

\*******************************************************************/

void slam_dumpt::process_labels(const std::list<irep_idt> &labels,
				const trace_stept &trace_step,
				slam_predicatest& slam_predicates)
{
  /* labels come shuffled, so unshuffle them */
  std::stack<irep_idt> rev_stack; /* stack to reverse labels */
  std::list<irep_idt> rev_labels;
  std::list<irep_idt>::const_iterator l_it;

  for (l_it = labels.begin(); l_it != labels.end(); l_it++)
    {
      const std::string &label = id2string(*l_it);

      if (!is_slam_label_L (label)) /* we don't need those */
	rev_stack.push (label);

      if(is_block_label (label) ||
         label == id2string(*(labels.rbegin())))
	{
	  while (!rev_stack.empty ())
	    {
	      rev_labels.push_back (rev_stack.top ());
	      rev_stack.pop ();
	    }
	}
    }
  
  /* check if we have a block label and SLIC_ERROR without instruction label */
  /* that's necessary because inserting "assert(false)" for SLIC_ERROR as done */
  /* in goto-convert cuts off our last instruction label */
  bool error_label = false;
  unsigned int block_index=0;
  bool instr_label = false;
  for (l_it = rev_labels.begin (); l_it != rev_labels.end(); l_it++)
    {
      const std::string &label = id2string(*l_it);
      if (is_block_label (label))
	block_index = get_block_index ('b', label);
      else
	{
	  instr_label |= is_instruction_label (label);
	  error_label |= is_error_label (label);
	}
    }
  /* if necessary, add an instruction label */
  if (error_label && !instr_label)
    {
      std::ostringstream ost ("c2bp_i_", std::ios_base::ate);
      ost << block_index << "_1";
      rev_labels.push_back (ost.str());
    }


  /* check if there are any c2bp labels for this state */
  for (l_it = rev_labels.begin(); l_it != rev_labels.end(); l_it++)
    {
      const std::string &label = id2string(*l_it);
      
      /* currently we don't care for anything else */
      if (!is_c2bp_label (label))
	continue;

      /* check if we are in malloc - Newton doesn't like malloc ;-)                   */
      const std::string &fname=
        trace_step.previous_PC->location.get_string("function");
        
      if (fname.find ("malloc_") != std::string::npos)
	continue;

      if (is_block_label (label))
	current_blocks[current_thread] = get_block_index ('b', label);
      else if (is_instruction_label (label))
	process_instr_label (label, trace_step, slam_predicates);
      else if (is_return_stmt_label (label))
	(splitted_trace[current_thread].back ()).is_return_stmt = true;
      else if (is_call_rtb_label (label))
	(splitted_trace[current_thread].back ()).call_return_block = 
	  get_block_index ('b', label);
      else if (is_calling_stmt_label (label))
	(splitted_trace[current_thread].back ()).is_calling_stmt = true;
    }
}

/*******************************************************************\

Function: slam_dumpt::process_instr_label

  Inputs: label, trace step, slam predicates

 Outputs: 

 Purpose: processes a label, generates the corresponding state info
          and pushes the info onto the stack of the corresponding
          thread

\*******************************************************************/

void
slam_dumpt::process_instr_label (const std::string &label,
				 const trace_stept &trace_step,
				 slam_predicatest& slam_predicates)
{
  unsigned block_number = get_block_index ('i', label);
  unsigned instruction_number = get_instruction_index (label);
  assert (block_number == current_blocks[current_thread]);

  /* previous state we encountered */
  const trace_stept &previous = *previous_thread_step[previous_thread];
  /* previous state of the current process */
  const trace_stept &previous_of_thread = *previous_thread_step[current_thread];

  /* get globals as they were before execution of current instruction */
  const std::string &pre_globals = get_global_state (previous, slam_predicates);
  /* get locals of current thread as they were before execution of current instruction */
  const std::string &pre_locals = get_local_state (previous/*_of_thread*/, slam_predicates, current_thread);

  const std::string fname=
    previous_of_thread.previous_PC->location.get_string("function");

  splitted_trace[current_thread].push_back
    (trace_infot (current_thread,
		  block_number,
		  instruction_number,
		  pre_globals,
		  pre_locals,
		  fname)
     );
  thread_step.push_back (current_thread);
}

/*******************************************************************\

Function: slam_dumpt::write_trace_to_file

  Inputs:

 Outputs: 

 Purpose: writes the split trace to a file

\*******************************************************************/

void slam_dumpt::write_trace_to_file (std::ofstream &file)
{
  std::vector<unsigned> thread_progress (thread_num);

  for (unsigned i = 0; i < thread_num; i++)
    {
      thread_progress[i] = 0;
    }
  previous_thread = 0; /* we assume the first thread has id 0 */

  for (unsigned count = 0; count < thread_step.size (); count ++)
    {
      unsigned step;
      current_thread = thread_step[count];
      
      step = thread_progress[current_thread];
      trace_infot &info = splitted_trace[current_thread][step];
      
      /* make sure we are in the right movie */
      assert (current_thread == info.thread_id);
      
      /* print out the state before execution of this instruction */
      file << current_thread << " "
	   << info.block << " "
	   << info.instruction << " " 
	   << info.pre_globals << info.pre_locals << "; // "
	   << info.function_name << std::endl;

      /* make progress ;-) */
      thread_progress[current_thread]++;
      previous_thread = current_thread;
    }
}

/*******************************************************************\

Function: symbolic_simulatort::dump_concurrent_trace_slam

  Inputs:

 Outputs: 

 Purpose: Dumps a concurrent trace (including thread IDs) that can
          parsed by Newton

\*******************************************************************/

void slam_dumpt::dump_concurrent_trace_slam()
{
  // strip .bp
  assert(slam_file.size()>3);
  assert(std::string(slam_file, slam_file.size()-3, 3)==".bp");
  
  std::string base_file_name(slam_file, 0, slam_file.size()-3);

  std::string path_file_name=base_file_name+".p";
  std::string predicates_file_name=base_file_name+".v";
  
  slam_predicatest slam_predicates(predicates_file_name);

  std::ofstream slam_path_file(path_file_name.c_str());

  std::cout << "Found counterexample with " 
	    << thread_num << " threads" << std::endl;

  /* adjust the size of the splitted trace and current blocks */
  splitted_trace.resize (thread_num);
  current_blocks.resize (thread_num);
  previous_thread_step.resize (thread_num);

  /* now split the trace into separate threads */
  split_trace (slam_predicates);

  /* splice the thing together again and print it */
  write_trace_to_file (slam_path_file);
}


