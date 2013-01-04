/*******************************************************************\

Module: Conversion to PROMELA

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#ifndef CPROVER_BOPPO_CONVERT_TO_PROMELA_H
#define CPROVER_BOPPO_CONVERT_TO_PROMELA_H

#include <iostream>

#include <context.h>

void convert_to_promela(const contextt &context,
                        std::ostream &out);

#endif
