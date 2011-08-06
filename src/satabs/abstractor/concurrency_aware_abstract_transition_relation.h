/*
 * concurrency_aware_abstract_transition_relation.h
 *
 *  Created on: Aug 2, 2011
 *      Author: alad
 */

#ifndef CONCURRENCY_AWARE_ABSTRACT_TRANSITION_RELATION_H_
#define CONCURRENCY_AWARE_ABSTRACT_TRANSITION_RELATION_H_

#include "abstract_transition_relation.h"

class concurrency_aware_abstract_transition_relationt : abstract_transition_relationt {
public:

	std::set<unsigned> from_passive_predicates, to_passive_predicates;
	valuest passive_values;

	concurrency_aware_abstract_transition_relationt();
	virtual ~concurrency_aware_abstract_transition_relationt();
};

#endif /* CONCURRENCY_AWARE_ABSTRACT_TRANSITION_RELATION_H_ */
