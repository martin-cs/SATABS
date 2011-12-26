/*******************************************************************\

Module: Predicate Manager

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>

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


exprt predicatest::make_expr_passive(
    const exprt& phi,
    const namespacet& ns,
    const unsigned subscript)
{
	// Recursively mutate the expression, to make it passive
  exprt tmp(phi);
	make_expr_passive_rec(tmp, ns, subscript);
  return tmp;
}

void predicatest::make_expr_passive_rec(
    exprt& phi,
    const namespacet& ns,
    const unsigned subscript)
{
  Forall_operands(it, phi)
    make_expr_passive_rec(*it, ns, subscript);

  if(phi.id()==ID_symbol)
  {
    symbol_exprt &phi_sym=to_symbol_expr(phi);
    const irep_idt &identifier=phi_sym.get_identifier();
    assert(identifier.as_string().find('#')==std::string::npos);
    if(is_procedure_local(ns.lookup(identifier)))
    {
      std::ostringstream os;
      os << identifier << '#' << subscript;
      phi_sym.set_identifier(os.str());
    }
  }
}

