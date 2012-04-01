/*******************************************************************\

Module: Predicate Abstraction of a Basic Block

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGAR_PREDICATE_IMAGE_SATQE_H
#define CPROVER_CEGAR_PREDICATE_IMAGE_SATQE_H

#include <vector>
#include <list>

#include <expr.h>

class message_handlert;
class symex_target_equationt;
class namespacet;

class abstract_transition_relationt;

void predicate_image_satqe(
    message_handlert &message_handler,
    const std::vector<exprt> &deref_curr_predicates,
    const std::vector<exprt> &deref_next_predicates,
    const std::list<exprt> &constaints,
    symex_target_equationt &equation,
    const namespacet &ns,
    abstract_transition_relationt &
    abstract_transition_relation);

#endif
