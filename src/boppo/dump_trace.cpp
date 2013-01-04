/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <fstream>

#include <context.h>
#include <prefix.h>

#include "simulator.h"
#include "slam_trace.h"

/*******************************************************************\

Function: simulator_baset::dump_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_baset::dump_trace(tracet &trace,
  const program_formulat::formula_goto_programt::instructiont &last_instruction)
{
  if(slam)
  {
    slam_dumpt slamd(program_formula, trace, last_instruction, slam_file);

    if (!slam_race)
      slamd.dump_trace_slam();
    else 
      slamd.dump_concurrent_trace_slam();
  }
  else if(compact_trace)
    dump_compact_trace(trace);
  else
    dump_full_trace(trace);
}

/*******************************************************************\

Function: simulator_baset::dump_full_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_baset::dump_full_trace(tracet &trace)
{
  unsigned count=1;
  
  for(tracet::const_iterator t_it=trace.begin();
      t_it!=trace.end();
      t_it++, count++)
  {
    const trace_stept &trace_step=*t_it;

    if(!trace_step.is_initial_state)
    {
      std::cout << "Executing Thread " << trace_step.previous_thread
                << ", "
                << trace_step.previous_PC->location
                << std::endl;
                
      const contextt context;
      const namespacet ns(context);
                
      trace_step.previous_program->
        output_instruction(ns, "", std::cout, trace_step.previous_PC);
        
      std::cout << std::endl;
    }

    if(!trace_step.is_error_state)
    {
      std::cout << "State " << count << std::endl;
      std::cout << "-------------------------------" << std::endl;
      
      unsigned no_globals=program_formula.no_globals;
      assert(trace_step.global_values.size()==no_globals);
      
      for(unsigned v=0; v<no_globals; v++)
      {
        std::cout << "  GLOBAL "
                  << program_formula.variables[v].display_name
                  << " = "
                  << trace_step.global_values[v] << std::endl;
      }
      
      for(unsigned t=0; t<trace_step.threads.size(); t++)
        for(unsigned v=0; v<program_formula.no_locals; v++)
        {
          assert(trace_step.threads[t].local_values.size()==
                 program_formula.no_locals);

          std::cout << "  LOCAL THREAD "
                    << t << " "
                    << program_formula.variables[v+no_globals].display_name
                    << " = "
                    << trace_step.threads[t].local_values[v] << std::endl;
        }
        
      std::cout << std::endl;
    }
  }
}

/*******************************************************************\

Function: simulator_baset::dump_compact_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_baset::dump_compact_trace(tracet &trace)
{
  tracet::const_iterator prev_it=trace.begin();
  
  if(prev_it==trace.end()) return;

  for(tracet::const_iterator t_it=++trace.begin(); // skip first
      t_it!=trace.end();
      prev_it=t_it, t_it++)
  {
    const trace_stept &from=*prev_it;
    const trace_stept &to=*t_it;
    statet::const_targett PC=to.previous_PC;

    // loops
    for(unsigned i=0; i<prev_it->loop_from.size(); i++)
      std::cout << "LOOP [" << std::endl;

    std::cout << "TRACE t=" << to.previous_thread;
      
    for(std::list<irep_idt>::const_iterator
        l_it=PC->labels.begin();
        l_it!=PC->labels.end();
        l_it++)
      std::cout << " " << *l_it;
                
    unsigned no_globals=from.global_values.size();

    for(unsigned v=0; v<no_globals; v++)
    {
      std::cout
        << " "
        << program_formula.variables[v].display_name
        << "="
        << from.global_values[v];
    }
    
    for(unsigned t=0; t<from.threads.size(); t++)
      for(unsigned v=0; v<from.threads[t].local_values.size(); v++)
      {
        std::cout
          << " "
          << program_formula.variables[no_globals+v].display_name
          << "="
          << from.threads[t].local_values[v];
      }
    
    if(PC->is_goto())
      std::cout << " TAKEN=" << to.state.data().taken;

    std::cout << std::endl;

    for(unsigned i=0; i<prev_it->loop_to.size(); i++)
      std::cout << "LOOP ]" << std::endl;
  }
}

