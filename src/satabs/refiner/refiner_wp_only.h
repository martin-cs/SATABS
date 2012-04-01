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

#ifndef CPROVER_SATABS_REFINER_WP_ONLY_H
#define CPROVER_SATABS_REFINER_WP_ONLY_H

#include "refiner_wp.h"

class refiner_wp_onlyt:public refiner_wpt
{
  public:
    refiner_wp_onlyt(
        const optionst &options,
        const argst &args) :
      refiner_wpt(options, args)
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

#endif /* CPROVER_SATABS_REFINER_WP_ONLY_H */
