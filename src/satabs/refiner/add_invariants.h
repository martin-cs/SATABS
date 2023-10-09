/*******************************************************************\

Module: The Concrete Model

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

#ifndef CPROVER_SATABS_ADD_INVARIANTS_H
#define CPROVER_SATABS_ADD_INVARIANTS_H

#include "../abstractor/abstract_program.h"

class concrete_modelt;
class predicatest;

void add_invariants(
    const concrete_modelt &concrete_model,
    abstract_programt::targett pc,
    const class predicatest &predicates);

#endif
