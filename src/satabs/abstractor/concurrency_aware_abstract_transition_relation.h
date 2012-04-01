/*
 * concurrency_aware_abstract_transition_relation.h
 *
 *  Created on: Aug 2, 2011
 *      Author: alad
 */

#ifndef CPROVER_SATABS_CONCURRENCY_AWARE_ABSTRACT_TRANSITION_RELATION_H
#define CPROVER_SATABS_CONCURRENCY_AWARE_ABSTRACT_TRANSITION_RELATION_H

#include "abstract_transition_relation.h"

class concurrency_aware_abstract_transition_relationt : public abstract_transition_relationt {
  public:

    // std::set<unsigned> from_passive_predicates, to_passive_predicates;
    valuest passive_values;

    concurrency_aware_abstract_transition_relationt();
    virtual ~concurrency_aware_abstract_transition_relationt();
};

#endif /* CPROVER_SATABS_CONCURRENCY_AWARE_ABSTRACT_TRANSITION_RELATION_H */
