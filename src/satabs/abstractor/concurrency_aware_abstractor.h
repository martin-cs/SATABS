/*
 * concurrency_aware_abstractor.h
 *
 *  Created on: Aug 2, 2011
 *      Author: alad
 */

#ifndef CONCURRENCY_AWARE_ABSTRACTOR_H_
#define CONCURRENCY_AWARE_ABSTRACTOR_H_

#include <memory>

#include "abstractor.h"

#include <util/std_expr.h>
#include <util/location.h>

#include <pointer-analysis/value_set_analysis.h>


class concurrency_aware_abstractort : public abstractort {
public:

	concurrency_aware_abstractort(const argst &args, std::auto_ptr<abstractort> specific_abstractor, const goto_functionst &functions) :
		abstractort(args),
		specific_abstractor(specific_abstractor),
		pointer_info(args.concrete_model.ns)
	{
		status("Performing pointer analysis for concurrency-aware abstraction");
		pointer_info(functions);
		status("Pointer analysis complete");
	}

	virtual ~concurrency_aware_abstractort()
	{

	}

protected:
	virtual void pred_abstract_block(
			goto_programt::const_targett target,
			const predicatest &predicates,
			abstract_transition_relationt &
			abstract_transition_relation);

	exprt make_passive(exprt phi);

	exprt make_passive_rec(exprt phi);

	std::set<symbol_exprt> targets_of_lvalue(const exprt& lvalue, goto_programt::const_targett program_location);

	bool broadcast_required(
	  		  goto_programt::const_targett target,
	  		  const predicatet &predicate,
	  		  goto_programt::const_targett program_location);

private:
	std::auto_ptr<abstractort> specific_abstractor;
	value_set_analysist pointer_info;


};

#endif /* CONCURRENCY_AWARE_ABSTRACTOR_H_ */
