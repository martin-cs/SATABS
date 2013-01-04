/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BOPPO_QUEUE_H
#define CPROVER_BOPPO_QUEUE_H

#include <deque>

#include "state.h"

class queuet
{
public:
  void add(const statet &state)
  {
    states.push_back(state);
  }

  statet next()
  {
    // this does BFS
    statet s=states.front();
    states.pop_front();
    return s;
  }
  
  bool empty() const
  {
    return states.empty();
  }

  typedef std::deque<statet> statest;
  statest states;
};

#endif
