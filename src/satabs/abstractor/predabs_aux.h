/*******************************************************************\

Module: Predicate Abstraction Auxiliary Code

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGAR_PREDABS_AUX
#define CPROVER_CEGAR_PREDABS_AUX

#include <set>
#include <list>
#include <vector>
#include <string>

#include <expr.h>
#include <solvers/prop/literal.h>
#include <goto-programs/goto_program.h>

class predicatest;
class prop_convt;

#if 0
void get_final_predicates(
    const std::vector<exprt> &predicates,
    goto_symex_statet &state,
    std::vector<exprt> &final_predicates);
#endif

literalt make_pos(
    const namespacet &ns,
    prop_convt &conv,
    const exprt &expr);

bool uses_symbol(const exprt &expr,
    const std::set<std::string> &symbols);

void build_equation(
    const namespacet &ns,
    const predicatest &predicates,
    goto_programt::const_targett target,
    std::list<exprt> &constraints,
    std::vector<exprt> &predicates_wp);

#endif
