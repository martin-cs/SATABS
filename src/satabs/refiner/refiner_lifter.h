/*******************************************************************\

Module: Refiner

Author: Daniel Kroening

Date: October 2008

Purpose: Calculate predicates for predicate abstraction using
         Interpolant Lifting

\*******************************************************************/

#ifndef CPROVER_SATABS_REFINER_LIFTER_H
#define CPROVER_SATABS_REFINER_LIFTER_H

#include "refiner_wp.h"

class refiner_liftert:public refiner_wpt
{
public:
  refiner_liftert(const argst &args, bool _prefix_first, unsigned max_predicates_to_add, bool prefer_non_pointer_predicates):
    refiner_wpt(args, _prefix_first, max_predicates_to_add, prefer_non_pointer_predicates)
  {
  }

protected:
  bool refine_prefix(
    predicatest &predicates, 
    abstract_modelt &abstract_model,
    const fail_infot &fail_info);
};

#endif
