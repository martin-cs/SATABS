/*
 * decide_validity_or_unsat.h
 *
 *  Used to decide whether expressions are valid, or unsatisfiable.
 *  This is used to eliminate redundant predicates
 *
 *  Created on: Mar 2, 2011
 *      Author: Alastair Donaldson
 */

#ifndef CPROVER_CHECK_REDUNDANCY_H_
#define CPROVER_CHECK_REDUNDANCY_H_

#include <expr.h>
#include <namespace.h>

bool is_valid(const exprt& e, const namespacet& ns);

bool is_unsatisfiable(const exprt& e, const namespacet& ns);

bool is_redundant(const exprt& predicate, const namespacet& ns);

void delete_unsatisfiable_cache();

#endif /* CPROVER_CHECK_REDUNDANCY_H_ */
