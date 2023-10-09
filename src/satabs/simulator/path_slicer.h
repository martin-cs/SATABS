/*******************************************************************\

Module: Path Slicer

Author: Daniel Kroening
    
Date: September 2006

Purpose:

\*******************************************************************/

#ifndef CPROVER_SATABS_PATH_SLICER_H
#define CPROVER_SATABS_PATH_SLICER_H

#include "../abstractor/abstract_program.h"

class namespacet;
class abstract_counterexamplet;

void path_slicer(
  const namespacet &ns,
  const abstract_functionst &abstract_functions,
  abstract_counterexamplet &abstract_counterexample);

#endif
