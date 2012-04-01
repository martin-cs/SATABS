/*******************************************************************\

Module: Create abstract expression from concrete one

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGAR_ABSTRACT_EXPRESSION_H
#define CPROVER_CEGAR_ABSTRACT_EXPRESSION_H

class exprt;
class predicatest;
class namespacet;

void abstract_expression(
  const predicatest &predicates,
  exprt &expr,
  const namespacet &ns);

#endif
