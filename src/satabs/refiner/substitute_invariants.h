/*******************************************************************\

Module: The Concrete Model

Author: Daniel Kroening

Date: May 2006

\*******************************************************************/

#ifndef CPROVER_SATABS_SUBSTITUTE_INVARIANTS_H
#define CPROVER_SATABS_SUBSTITUTE_INVARIANTS_H

#include "../abstractor/abstract_program.h"

class concrete_modelt;
class exprt;

void substitute_invariants(
    const concrete_modelt &concrete_model,
    abstract_programt::targett pc,
    exprt &predicate);

#endif
