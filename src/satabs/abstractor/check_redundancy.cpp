/*
 * check_redundancy.cpp
 *
 *  Created on: Mar 2, 2011
 *      Author: Alastair Donaldson
 */

#include <map>
#include <memory>

#include <std_expr.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include "check_redundancy.h"

static std::auto_ptr<std::map<exprt, bool> > is_unsatisfiable_cache;

/*******************************************************************\

Function: is_valid

  Inputs: expression e, and namespace ns

 Outputs: returns true iff e is valid

 Purpose: decides (using SAT) whether expression e is valid

\*******************************************************************/

bool is_valid(const exprt& e, const namespacet& ns)
{
  return is_unsatisfiable(not_exprt(e), ns);
}

/*******************************************************************\

Function: is_unsatisfiable

  Inputs: expression e, and namespace ns

 Outputs: returns true iff e is unsatisfiable

 Purpose: decides (using SAT) whether expression e is unsatisfiable

\*******************************************************************/

bool is_unsatisfiable(const exprt& e, const namespacet& ns)
{
  if(NULL == is_unsatisfiable_cache.get())
  {
    is_unsatisfiable_cache = std::auto_ptr<std::map<exprt, bool> >(new std::map<exprt, bool>);
  }

  std::map<exprt, bool>::const_iterator it = is_unsatisfiable_cache->find(e);
  if(is_unsatisfiable_cache->end() != it)
  {
    return it->second;
  }

  satcheckt satcheck;
  bv_pointerst solver(ns, satcheck);
  solver.set_to_true(e);

  switch(solver.dec_solve())
  {
    case decision_proceduret::D_UNSATISFIABLE:
      (*is_unsatisfiable_cache)[e] = true;
      return true;

    case decision_proceduret::D_SATISFIABLE:
        (*is_unsatisfiable_cache)[e] = false;
      return false;

    default:
      throw "unexpected result from dec_solve()";
    }
}


/*******************************************************************\

Function: is_redundant

  Inputs: expression predicate, and namespace ns

 Outputs: returns true iff e is either valid or unsatisfiable

 Purpose: decides (using SAT) whether expression is worth adding as
          a predicate.  It is not worth adding (i.e., it is redundant)
          if it is either valid, or unsatisfiable

\*******************************************************************/

bool is_redundant(const exprt& predicate, const namespacet& ns)
{
  return is_valid(predicate, ns) || is_unsatisfiable(predicate, ns);
}

void delete_unsatisfiable_cache()
{
  if(NULL != is_unsatisfiable_cache.get())
  {
    is_unsatisfiable_cache = std::auto_ptr<std::map<exprt, bool> >(NULL);
  }
}
