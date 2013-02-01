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
#include <options.h>

#include <solvers/prop/prop.h>

#include "../loop_component.h"
#include "../abstractor/abstract_program.h"

class fail_infot;
class predicatest;
class abstract_modelt;

class refinert:public loop_componentt
{
public:
  refinert(
      const optionst &options,
      const argst &args) :
    loop_componentt(args),
    max_predicates_to_add(options.get_int_option("max-new-predicates")),
    prefer_non_pointer_predicates(options.get_bool_option("prefer-non-pointer-predicates")),
    remove_equivalent_predicates(options.get_bool_option("remove-equivalent-predicates")),
    no_mixed_predicates(options.get_bool_option("no-mixed-predicates"))
  {
    reset_num_predicates_added();
  }

  virtual void refine(
      predicatest &predicates, 
      abstract_modelt &abstract_model,
      const fail_infot &fail_info)=0;

  bool get_no_mixed_predicates() const
  {
    return no_mixed_predicates;
  }

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

  bool is_satisfiable(propt &prop)
  {
    prop.set_message_handler(get_message_handler());
    prop.set_verbosity(get_verbosity());

    // solve it
    switch(prop.prop_solve())
    {
      case propt::P_UNSATISFIABLE:
        return false;

      case propt::P_SATISFIABLE:
        return true;

      default:
        throw "unexpected result from prop_solve()";
    }
  }

  const unsigned max_predicates_to_add;
  unsigned num_predicates_added;
  const bool prefer_non_pointer_predicates;
  const bool remove_equivalent_predicates;
  const bool no_mixed_predicates;

  void reset_num_predicates_added()
  {
    num_predicates_added = 0;
  }
};

#endif
