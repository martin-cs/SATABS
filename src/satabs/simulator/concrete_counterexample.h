/*******************************************************************\

Module: Counterexamples

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_COUNTEREXAMPLE_H
#define CPROVER_CEGAR_COUNTEREXAMPLE_H

#include <goto-programs/goto_trace.h>

/* A concrete conterexample */

class concrete_counterexamplet
{
public:
  goto_tracet goto_trace;

  void clear()
  {
    goto_trace.clear();
  }
};

void show_counterexample(
  std::ostream &out,
  const symbol_tablet &symbol_table,
  const concrete_counterexamplet &counterexample);

std::ostream& operator<< (
  std::ostream& out,
  const concrete_counterexamplet &counterexample);

#endif
