/*******************************************************************\

Module: The Empty Refiner

Author: Daniel Kroening

Date: November 2009

Purpose: Do nothing.

\*******************************************************************/

#ifndef CPROVER_SATABS_NO_REFINER_H
#define CPROVER_SATABS_NO_REFINER_H

#include "refiner.h"

class no_refinert:public refinert
{
public:
  explicit no_refinert(const optionst &options):
    refinert(options)
  {
  }

  virtual void refine(
    predicatest &predicates, 
    abstract_modelt &abstract_model,
    const fail_infot &fail_info)
  {
    // we really do nothing!
  }

};

#endif
