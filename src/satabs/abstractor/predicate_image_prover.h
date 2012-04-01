/*******************************************************************\

Module: Predicate Abstraction of a Basic Block

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGAR_PREDICATE_IMAGE_PROVER_H
#define CPROVER_CEGAR_PREDICATE_IMAGE_PROVER_H

#include <vector>
#include <list>

#include <expr.h>

class symex_target_equationt;
class message_handlert;
class abstract_transition_relationt;

void predicate_image_prover(
    message_handlert *message_handler,
    const std::vector<exprt> &curr_predicates,
    const std::vector<exprt> &next_predicates,
    const std::vector<exprt> &predicates_wp,
    const std::list<exprt> &constaints,
    const symex_target_equationt &equation,
    const namespacet &ns,
    abstract_transition_relationt &abstract_transition_relation);

#endif
