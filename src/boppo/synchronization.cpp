/*******************************************************************\

Module: Compute Interleaving with Partial Order Reduction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include "simulator.h"

/*******************************************************************\

Function: simulatort::synchronization

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::synchronization(
  const statet &state,
  queuet &queue)
{
  // first pass: get the threads that try to synchronize
  
  typedef std::map<irep_idt, std::set<unsigned> > event_mapt;
  event_mapt event_map;

  for(unsigned i=0; i<state.data().threads.size(); i++)
  {
    // end of thread?
    if(state.data().threads[i].is_at_end())
      continue;
      
    // get instruction
    //const instructiont &instruction=*state.data().threads[i].PC;
  }
  
  // now see which ones we have twice
  for(event_mapt::const_iterator it=event_map.begin();
      it!=event_map.end();
      it++)
  {
    const std::set<unsigned> &threads=it->second;
    unsigned number_of_threads=threads.size();
    
    assert(number_of_threads<=2);
    
    if(number_of_threads==2)
    {
      // do it
      unsigned t1=*threads.begin();
      unsigned t2=*(++threads.begin());

      statet new_state=state;
      new_state.set_previous(state, t1);
      new_state.data_w().threads[t1].PC++;
      new_state.data_w().threads[t2].PC++;
      queue.add(new_state);

      // just take the first one, that is enough
      return;
    }
  }
}
