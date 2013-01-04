/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <time_stopping.h>
#include <threeval.h>

//#include <config.h>

#include "simulator.h"
#include "state_projection.h"

/*******************************************************************\

Function: simulatort::compute_successor_states

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::compute_successor_states(
  const statet &state,
  bool check_property,
  queuet &queue)
{
  #ifdef DEBUG
  std::cout << "simulatort::compute_successor_states1" << std::endl;
  #endif
  
  // see if there are any threads that try to synchronize
  synchronization(state, queue);
  
  // now do regular statements

  interleavingt interleaving;
  compute_interleaving(state, interleaving);
  
  for(interleavingt::const_iterator
      i_it=interleaving.begin();
      i_it!=interleaving.end();
      i_it++)
  {
    execute_thread(state, *i_it, check_property, queue);
    if(error_state_found) return;
  }
  
  #ifdef DEBUG
  std::cout << "simulatort::compute_succesor_states2" << std::endl;
  #endif
}

/*******************************************************************\

Function: simulatort::simulator

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::simulator()
{
  std::cout << "Starting Symbolic Simulation"
            << std::endl;

  #ifdef DEBUG
  std::cout << "simulatort::simulator1\n";
  #endif

  queuet queue;
  queue.add(make_initial_state());
  
  #ifdef DEBUG
  std::cout << "simulatort::simulator2\n";
  #endif

  run(queue);

  #ifdef DEBUG
  std::cout << "simulatort::simulator3\n";
  #endif
}

/*******************************************************************\

Function: simulatort::run

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::run(queuet &queue)
{
  fine_timet start_time=current_time();

  error_state_found=false;

  #ifdef DEBUG
  std::cout << "simulatort::run1\n";
  #endif

  unsigned counter=0;

  state_projectiont state_projection(formula_container, program_formula);
  
  while(!queue.empty() && !error_state_found)
  {
    #ifdef DEBUG
    std::cout << "simulatort::run2\n";
    #endif

    counter++;
    explore(queue.next(), queue);
  }

  if(error_state_found)
    std::cout << "VERIFICATION FAILED" << std::endl;
  else
    std::cout << "VERIFICATION SUCCESSFUL" << std::endl;

  std::cout << std::endl;
  std::cout << "States explored: " << counter << std::endl;
  std::cout << "Runtime: ";
  output_time(current_time()-start_time, std::cout);
  std::cout << std::endl;
}

/*******************************************************************\

Function: simulatort::explore

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::explore(
  const statet &state,
  queuet &queue)
{
  #ifdef DEBUG
  std::cout << "simulatort::explore1\n";
  #endif

  #if 0
  std::cout << "/////////////////////////////////////////////// "
            << "\n";

  for(unsigned thread=0; thread<program_formula.threads.size(); thread++)
  {
    std::cout << "Thread " << thread << " Location: ";
    if(state.data().PCs[thread]==
       program_formula.threads[thread].formula_goto_program.instructions.end())
      std::cout << "END" << std::endl;
    else
    {
      instructiont &instruction=*state.data().PCs[thread];
      std::cout << location_string(instruction.location) << std::endl;
    }
  }
  std::cout << std::endl;
  #endif

  // dump it if the guard is false
  if(state.data().guard.is_false())
    return;
    
  #ifdef DEBUG
  std::cout << "simulatort::explore2\n";
  #endif
  
  if(history.check_history(
    state, enable_qbf_cache, enable_small_history))
  {
    // we have seen it already
    #ifdef DEBUG
    std::cout << ">>>>>>>>>>>>>>>>>>>>>>>> SEEN ALREADY\n";
    #endif
    return;
  }
  
  #ifdef DEBUG
  std::cout << "simulatort::explore3\n";
  #endif
  
  compute_successor_states(state, true, queue);
  
  #ifdef DEBUG
  std::cout << "simulatort::explore4\n";
  #endif
}
