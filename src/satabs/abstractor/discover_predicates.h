/*******************************************************************\

Module: Predicate Discovery

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGAR_DISCOVER_PREDICATES_H
#define CPROVER_CEGAR_DISCOVER_PREDICATES_H

#include <set>

#include "predicates.h"

class namespacet;

void discover_predicates(
    const exprt &expr,
    std::set<predicatet> &predicates,
    const namespacet &ns,
    const bool no_mixed_predicates);

#endif
