/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <solvers/sat/satcheck.h>

#include "compare_states.h"
#include "simulator.h"

/*******************************************************************\

Function: match

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool match(
  formula_containert &container,
  const statet &state,
  const std::map<vart, bool> &values)
{
  // do the reset
  container.reset_prop();

  // build the SAT instance
  satcheckt satcheck;

  // 1st, the guard must hold
  {
    literalt l=state.data().guard.convert(satcheck);
    satcheck.l_set_to(l, true);
  }

  #if 0
  std::cout << "G: ";
  state.data().guard.output(std::cout);
  std::cout << std::endl;
  #endif
  
  // 2nd, the values must match
  for(std::map<vart, bool>::const_iterator
      it=values.begin();
      it!=values.end();
      it++)
  {
    const vart &var=it->first;
    formulat f=state.data().get_var(var.var_nr, var.thread_nr);
    literalt l=f.convert(satcheck);
    satcheck.l_set_to(l, it->second);
    
    #if 0
    std::cout << "V: ";
    state.data().values[v].output(std::cout);
    std::cout << std::endl;
    #endif
  }
  
  std::cout << "Running " << satcheck.solver_text() << ", "
            << satcheck.no_variables() << " variables, "
            << satcheck.no_clauses() << " clauses" << std::endl;

  switch(satcheck.prop_solve())
  {
  case propt::P_SATISFIABLE:
    // oh! match!
    return true;
    
  case propt::P_UNSATISFIABLE:
    // nah, no match
    return false;
    
  default:;
    assert(false);
  }

  assert(false);
  return false;
}

/*******************************************************************\

Function: simulatort::loop_detection

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::loop_detection(tracet &trace)
{
  // walk down the trace, look for potential loops
  
  std::cout << "Loop Detection" << std::endl;

  for(tracet::iterator f_it=trace.begin();
      f_it!=trace.end();
      f_it++)
  {
    trace_stept &from_step=*f_it;
    
    // get successor states
    queuet queue;
    compute_successor_states(from_step.state, false, queue);
    
    bool match_found=false;
    
    // compare the successors with what we have on the trace
    // this is quadratic in trace.size()
    for(queuet::statest::const_iterator
        q_it=queue.states.begin();
        q_it!=queue.states.end() && !match_found;
        q_it++)
    {
      const statet &new_state=*q_it;
      
      if(!new_state.is_backwards_jump())
        continue;

      #if 0
      std::cout << "COMPARE " << queue.size() << "\n";
      #endif

      // first compare PCs
      for(tracet::iterator t_it=trace.begin();
          t_it!=f_it && !match_found;
          t_it++)
      {
        const trace_stept &to_step=*t_it;
        
        if(to_step.compare_PCs(new_state))
        {
          #if 0
          std::cout << "PC MATCH\n";
          #endif
          
          std::map<vart, bool> values;
          
          // this should be restricted to the active variables
          for(unsigned v=0; v<to_step.global_values.size(); v++)
            values[vart(v)]=to_step.global_values[v];

          for(unsigned t=0; t<new_state.data().threads.size(); t++)
            for(unsigned v=0; v<new_state.data().threads[t].locals.size(); v++)
            {
              unsigned v2=to_step.global_values.size()+v;
              values[vart(v2, t)]=to_step.threads[t].local_values[v];
            }
            
          // now see if data can be made to match
          // use data from trace for old state
          if(match(formula_container, new_state, values))
          {
            // oh, yes! a match!
            match_found=true;

            // avoid duplicates for now
            if(f_it->loop_from.empty() && f_it->loop_to.empty() &&
               t_it->loop_from.empty() && t_it->loop_to.empty())
              add_loop(f_it, t_it);
            
            #if 0
            std::cout << "MATCH\n";
            #endif
          }
        }
      }
    }
  }
}
