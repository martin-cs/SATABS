/*******************************************************************\

Module: Functions for deciding whether locations of expressions
intersect, using pointer information

Author: Alastair Donaldson

Date: August 2011

\*******************************************************************/

#ifndef CPROVER_SATABS_LOCATIONS_OF_EXPRESSIONS_H
#define CPROVER_SATABS_LOCATIONS_OF_EXPRESSIONS_H

#include <set>

#include <std_expr.h>

#include <goto-programs/goto_program.h>

#include "predicates.h"

class value_set_analysist;


bool locations_intersect(const predicatet& phi,
    const predicatet& psi,
    const goto_programt::const_targett program_location,
    value_set_analysist& pointer_info,
    const namespacet& ns);

std::set<symbol_exprt> locations_of_expression(
    const predicatet& phi,
    const goto_programt::const_targett program_location,
    value_set_analysist& pointer_info,
    const namespacet& ns);

std::set<symbol_exprt> locations_of_expression_rec(
    const predicatet& phi,
    const goto_programt::const_targett program_location,
    value_set_analysist& pointer_info,
    const namespacet& ns);


#endif
