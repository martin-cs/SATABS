/*******************************************************************\

Module: Predicate Discovery

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGAR_LIFT_IF_H
#define CPROVER_CEGAR_LIFT_IF_H

class exprt;

bool has_non_boolean_if(const exprt &expr);
void lift_if(exprt &expr);

#endif
