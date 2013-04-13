/*******************************************************************\

Module: Conversion to PROMELA

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#ifndef CPROVER_BOPPO_CONVERT_TO_PROMELA_H
#define CPROVER_BOPPO_CONVERT_TO_PROMELA_H

#include <iostream>

#include <util/symbol_table.h>

void convert_to_promela(const symbol_tablet &symbol_table,
                        std::ostream &out);

#endif
