/*
 * decide_validity_or_unsat.h
 *
 *  Used to decide whether expressions are valid, or unsatisfiable.
 *  This is used to eliminate redundant predicates
 *
 *  Created on: Mar 2, 2011
 *      Author: Alastair Donaldson
 */

#ifndef CPROVER_SATABS_CHECK_REDUNDANCY_H
#define CPROVER_SATABS_CHECK_REDUNDANCY_H

class exprt;
class namespacet;

bool is_equivalent(const exprt& e1, const exprt& e2, const namespacet& ns);

bool is_valid(const exprt& e, const namespacet& ns);

bool is_unsatisfiable(const exprt& e, const namespacet& ns);

bool is_redundant(const exprt& predicate, const namespacet& ns);

void delete_unsatisfiable_cache();

#endif /* CPROVER_SATABS_CHECK_REDUNDANCY_H */
