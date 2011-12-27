/*
 * refiner_wp_only.h
 *
 * This overrides refiner_wp, and disables transition refinement.
 * This is in the context of concurrent predicate abstraction, where it is
 * not clear to us (yet) how transition refinement should work
 *
 *  Created on: Dec 21, 2010
 *      Author: ally
 */

#ifndef REFINER_WP_ONLY_H_
#define REFINER_WP_ONLY_H_

class refiner_wp_onlyt:public refiner_wpt
{
public:
  refiner_wp_onlyt(
      const argst &args,
      bool _prefix_first,
      unsigned max_predicates_to_add,
      bool prefer_non_pointer_predicates,
      bool no_mixed_predicates,
      bool passive_constrain):
    refiner_wpt(args, _prefix_first,
        max_predicates_to_add, prefer_non_pointer_predicates,
        no_mixed_predicates, passive_constrain)
  {
  }

protected:
  virtual bool check_transitions(
    const predicatest &predicates,
    abstract_modelt &abstract_model,
    const fail_infot &fail_info)
  {
	  // This refiner does not even try to check the transitions
	  print(9, "Not refining transitions -- this is disabled.");
	  return true;
  }

};

#endif /* REFINER_WP_ONLY_H_ */
