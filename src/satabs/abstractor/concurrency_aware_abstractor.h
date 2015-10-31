/*
 * concurrency_aware_abstractor.h
 *
 *  Created on: Aug 2, 2011
 *      Author: alad
 */

#ifndef CPROVER_SATABS_CONCURRENCY_AWARE_ABSTRACTOR_H
#define CPROVER_SATABS_CONCURRENCY_AWARE_ABSTRACTOR_H

#include <util/std_expr.h>

#include <pointer-analysis/value_set_analysis.h>

#include "../prepare/concrete_model.h"
#include "abstractor.h"

class concurrency_aware_abstractort : public abstractort
{
public:
  concurrency_aware_abstractort(
      std::auto_ptr<abstractort> specific_abstractor,
      const bool _passive_nondet);

  virtual ~concurrency_aware_abstractort()
  {
  }

protected:
  virtual void pred_abstract_block(
      goto_programt::const_targett target,
      const predicatest &predicates,
      abstract_transition_relationt &
      abstract_transition_relation);

  virtual void abstract_expression(
      const predicatest &predicates,
      exprt &expr,
      const namespacet &ns,
      goto_programt::const_targett program_location);

  virtual void abstract_assume_guard(
      const predicatest &predicates,
      exprt &expr,
      const namespacet &ns,
      goto_programt::const_targett program_location);

  std::set<symbol_exprt> targets_of_lvalue(
    const exprt& lvalue,
    goto_programt::const_targett program_location);

  bool broadcast_required(
      goto_programt::const_targett target,
      const predicatet &predicate);

  virtual void set_concrete_model(const concrete_modelt &_concrete_model)
  {
    specific_abstractor->set_concrete_model(_concrete_model);
    concrete_model=&_concrete_model;
    delete pointer_info;
    pointer_info=new value_set_analysist(concrete_model->ns);
    status() << "Performing pointer analysis for concurrency-aware abstraction" << eom;
    (*pointer_info)(concrete_model->goto_functions);
    status() << "Pointer analysis complete" << eom;
  }

private:
  std::auto_ptr<abstractort> specific_abstractor;
  const bool passive_nondet;
  value_set_analysist *pointer_info;
};

#endif /* CPROVER_SATABS_CONCURRENCY_AWARE_ABSTRACTOR_H */
