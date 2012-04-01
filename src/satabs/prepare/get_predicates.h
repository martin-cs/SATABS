/*******************************************************************\

Module: Get user-provided predicates

Author: Daniel Kroening

Date: March 2011

Purpose: 

\*******************************************************************/

#ifndef CPROVER_SATABS_GET_PREDICATES_H
#define CPROVER_SATABS_GET_PREDICATES_H

#include <string>
#include <vector>

#include <expr.h>

class message_handlert;
class namespacet;

void get_predicates(
    const std::string &file,
    message_handlert &message_handler,
    const namespacet &ns,
    std::vector<exprt> &predicates);

#endif
