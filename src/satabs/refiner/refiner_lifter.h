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
    refiner_liftert(
        const optionst &options,
        const argst &args) :
      refiner_wpt(options, args)
  {
  }

  protected:
    bool refine_prefix(
        predicatest &predicates, 
        abstract_modelt &abstract_model,
        const fail_infot &fail_info);
};

#endif
