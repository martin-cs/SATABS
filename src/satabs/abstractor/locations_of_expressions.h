/*******************************************************************\

Module: Functions for deciding whether locations of expressions
        intersect, using pointer information

Author: Alastair Donaldson

  Date: August 2011

\*******************************************************************/

#ifndef LOCATIONS_OF_EXPRESSIONS_H
#define LOCATIONS_OF_EXPRESSIONS_H

#include "predicates.h"

#include <goto-programs/goto_program.h>
#include <pointer-analysis/value_set_analysis.h>
#include <util/std_expr.h>

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
