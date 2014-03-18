/*******************************************************************\

Module: "Preprocess" C Functions for CEGAR

Author: Daniel Kroening

Date:   September 2009

Purpose: 

\*******************************************************************/

#ifndef CPROVER_SATABS_PREPARE_FUNCTIONS_H
#define CPROVER_SATABS_PREPARE_FUNCTIONS_H

#include <goto-programs/goto_functions.h>

class symbol_tablet;
class message_handlert;

void prepare_functions(
    symbol_tablet &symbol_table,
    goto_functionst &goto_functions,
    message_handlert &message_handler);

#endif
