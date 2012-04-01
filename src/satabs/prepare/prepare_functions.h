/*******************************************************************\

Module: "Preprocess" C Functions for CEGAR

Author: Daniel Kroening

Date:   September 2009

Purpose: 

\*******************************************************************/

#ifndef CPROVER_SATABS_PREPARE_FUNCTIONS_H
#define CPROVER_SATABS_PREPARE_FUNCTION_H

#include <goto-programs/goto_functions.h>

class contextt;
class message_handlert;

void prepare_functions(
    contextt &context,
    goto_functionst &goto_functions,
    message_handlert &message_handler);

#endif
