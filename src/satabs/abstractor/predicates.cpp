/*******************************************************************\

Module: Predicate Manager

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <langapi/language_util.h>

#include "predicates.h"

#include <std_expr.h>
#include <context.h>
#include <namespace.h>

/*******************************************************************\

Function: predicatest::lookup

  Inputs:

 Outputs:

 Purpose: find (and add, if not found) a predicate

\*******************************************************************/

unsigned predicatest::lookup(const predicatet &predicate)
{
  std::pair<predicate_mapt::iterator, bool> result=
    predicate_map.insert(
    std::pair<predicatet, unsigned>
    (predicate, predicate_vector.size()));

  if(result.second) // already there?
  {
    // actually inserted
    predicate_vector.push_back(result.first);
  }

  return result.first->second;
}

/*******************************************************************\

Function: operator<<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream& operator<< (std::ostream& out,
                          const predicatest &predicates)
{
  for(unsigned i=0; i<predicates.size(); i++)
  {
    contextt context;
    namespacet ns(context);
    out << "b" << i << " <=> "
        << from_expr(ns, "", predicates[i]) << std::endl;
  }

  return out;
}

/*******************************************************************\

Function: operator==

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator== (const predicatest &p1, const predicatest &p2)
{
  return p1.predicate_vector==p2.predicate_vector;
}


exprt predicatest::make_expr_passive(const exprt& phi, const namespacet& ns)
{
	// Recursively mutate the expression, to make it passive
  exprt tmp(phi);
	make_expr_passive_rec(tmp, ns);
  return tmp;
}

void predicatest::make_expr_passive_rec(exprt& phi, const namespacet& ns)
{
  Forall_operands(it, phi)
    make_expr_passive_rec(*it, ns);

  if(phi.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_expr(phi).get_identifier();
    assert(*identifier.as_string().rbegin()!='$');
    if(is_procedure_local(ns.lookup(identifier)))
      phi.set(ID_identifier, identifier.as_string()+"$");
  }
}

