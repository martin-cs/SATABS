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

Function: is_equivalent

Inputs: expression e1, expression e2, and namespace ns

Outputs: returns true if e1 and e2 are  equivalent, i.e. under all
valuations their values equal. The other implication might
not hold (for speed purposes we employ some heuristics)

Purpose: decides (using SAT) whether expression e1 is equivalent
to expression e2

\*******************************************************************/

bool is_equivalent(const exprt& e1, const exprt& e2, const namespacet& ns)
{
  irep_idt i1 = e1.id();
  irep_idt i2 = e2.id();

  //for speedup do some quick checks that mostly imply non-equivalence
  if (i1 == ID_equal &&
      (i2 == ID_lt || i2 == ID_gt || i2==ID_le || i2==ID_ge))
    return false;

  if (i2 == ID_equal &&
      (i1 == ID_lt || i1 == ID_gt || i1==ID_le || i1==ID_ge))
    return false;

  return is_valid(equal_exprt(e1,e2), ns);
}

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
  if(!is_unsatisfiable_cache.get())
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
  if(is_unsatisfiable_cache.get())
  {
    is_unsatisfiable_cache = std::auto_ptr<std::map<exprt, bool> >(0);
  }
}
