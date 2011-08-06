/*******************************************************************\

Module: Refiner

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

Purpose: Calculate predicates for predicate abstraction.

\*******************************************************************/

#ifndef CPROVER_CEGAR_REFINER_H
#define CPROVER_CEGAR_REFINER_H

#include <decision_procedure.h>

#include "../loop_component.h"
#include "../abstractor/predicates.h"
#include "../simulator/fail_info.h"

class refinert:public loop_componentt
{
public:
  refinert(const argst &args, const unsigned max_predicates_to_add = (unsigned)(-1), const bool prefer_non_pointer_predicates = false):
    loop_componentt(args), max_predicates_to_add(max_predicates_to_add), prefer_non_pointer_predicates(prefer_non_pointer_predicates)
  {
	  reset_num_predicates_added();
  }

  virtual void refine(
    predicatest &predicates, 
    abstract_modelt &abstract_model,
    const fail_infot &fail_info)=0;

protected:
  typedef enum { FROM, TO } wheret;

  void add_predicates(
    abstract_programt::targett pc,
    predicatest &predicates,
    const exprt &expr,
    bool &found_new,
    wheret where);

  bool is_satisfiable(decision_proceduret &decision_procedure)
  {
    decision_procedure.set_message_handler(get_message_handler());
    decision_procedure.set_verbosity(get_verbosity());
  
    // solve it
    switch(decision_procedure.dec_solve())
    {
    case decision_proceduret::D_UNSATISFIABLE:
      return false;

    case decision_proceduret::D_SATISFIABLE:
      return true;

    default:
      throw "unexpected result from dec_solve()";
    }
  }

  const unsigned max_predicates_to_add;
  unsigned num_predicates_added;
  const bool prefer_non_pointer_predicates;

  void reset_num_predicates_added()
  {
	  num_predicates_added = 0;
  }

};

#endif
