/*******************************************************************\

Module: Variable Mapping HDL<->C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGAR_MAP_VARS_H
#define CPROVER_CEGAR_MAP_VARS_H

#include <util/symbol_table.h>
#include <util/message.h>
#include <util/replace_expr.h>

#include "concrete_model.h"

#if 0
void map_vars(symbol_tablet &symbol_table,
    const std::list<concrete_transition_systemt> &modules,
    replace_mapt &replace_map,
    message_handlert *message);

bool is_program_symbol(const symbolt &symbol);
#endif

#endif
