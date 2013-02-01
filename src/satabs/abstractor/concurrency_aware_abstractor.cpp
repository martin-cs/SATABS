/*
 * concurrency_aware_abstractor.cpp
 *
 *  Created on: Aug 2, 2011
 *      Author: alad
 */

#include <cstdlib>
#include <algorithm>
#include <iterator>

#include <ansi-c/c_types.h>

#include <arith_tools.h>
#include <string2int.h>

#include "concurrency_aware_abstractor.h"
#include "concurrency_aware_abstract_transition_relation.h"
#include "locations_of_expressions.h"
#include "predabs_aux.h"
#include "../prepare/concrete_model.h"

static void adjust_pred_index(exprt& expr,
    const predicatest& all_preds,
    const predicatest& passive_preds)
{
  Forall_operands(it, expr)
    adjust_pred_index(*it, all_preds, passive_preds);

  if(expr.id()==ID_predicate_symbol)
  {
    unsigned p=safe_str2unsigned(expr.get(ID_identifier).c_str());
    if(p >= passive_preds.size())
    {
      bool found=passive_preds.find(all_preds[p], p);
      assert(found);
      expr.id(ID_predicate_passive_symbol);
      expr.set(ID_identifier, p);
    }
  }
}

concurrency_aware_abstractort::concurrency_aware_abstractort(
    const argst &args,
    std::auto_ptr<abstractort> specific_abstractor,
    const bool _passive_nondet) :
  abstractort(args),
  specific_abstractor(specific_abstractor),
  pointer_info(args.concrete_model.ns),
  passive_nondet(_passive_nondet)
{
  status("Performing pointer analysis for concurrency-aware abstraction");
  pointer_info(args.concrete_model.goto_functions);
  status("Pointer analysis complete");
}


void concurrency_aware_abstractort::pred_abstract_block(
    goto_programt::const_targett target,
    const predicatest &predicates,
    abstract_transition_relationt &
    abstract_transition_relation)
{
  concurrency_aware_abstract_transition_relationt* concurrency_aware_abstract_transition_relation = dynamic_cast<concurrency_aware_abstract_transition_relationt*>(&abstract_transition_relation);
  assert(concurrency_aware_abstract_transition_relation);

  // Do standard PA on the assignment
  this->specific_abstractor->pred_abstract_block(target, predicates, abstract_transition_relation);

  // Now do PA on passive threads
  predicatest passive_predicates;

  predicatest all_predicates; // Active then passive.  Order matters here!!!

  for(unsigned int i = 0; i < predicates.size(); i++)
  {
    // Add existing predicates (lookup does this)
    all_predicates.lookup(predicates[i]);
  }


  for(unsigned int i = 0; i < predicates.size(); i++)
  {
    // Add passive versions of existing predicates (lookup does this)
    passive_predicates.lookup(predicatest::make_expr_passive(predicates[i], concrete_model.ns, 0));
    all_predicates.lookup(predicatest::make_expr_passive(predicates[i], concrete_model.ns, 0));
  }


  std::vector<exprt> passive_predicates_wp;

  std::list<exprt> passive_constraints;

  build_equation(
      concrete_model.ns,
      passive_predicates,
      target,
      passive_constraints,
      passive_predicates_wp);
  
  bool passive_broadcast_only = false;
  // __CPROVER_passive_broadcast label enforces broadcast
  for(goto_programt::instructiont::labelst::const_iterator
      l=target->labels.begin();
      !passive_broadcast_only && l!=target->labels.end();
      ++l)
    passive_broadcast_only = *l=="__CPROVER_passive_broadcast";

  for(unsigned int i = 0; i < predicates.size(); i++)
  {
    if((passive_predicates_wp[i]==passive_predicates[i] ||
        predicates[i]==predicatest::make_expr_passive(predicates[i], concrete_model.ns, 0)) &&
        (!passive_broadcast_only ||
         abstract_transition_relation.values.find(i)==abstract_transition_relation.values.end()))
    {
      concurrency_aware_abstract_transition_relation->passive_values.erase(i);
#ifdef DEBUG
      std::cout << "UNCHANGED: P" << i << "$ ~ (" << from_expr(concrete_model.ns, "", passive_predicates[i]) << ")" << std::endl << std::endl;
#endif
    }
    else
    {
#ifdef DEBUG
      std::cout << "DIFFERENT: P" << i << "$ ~ (" << from_expr(concrete_model.ns, "", passive_predicates[i]) << ")" << std::endl;
      std::cout << "WP: " << from_expr(concrete_model.ns, "", passive_predicates_wp[i]) << std::endl;
      std::cout << "P:  " << from_expr(concrete_model.ns, "", passive_predicates[i]) << std::endl;
#endif

      const bool bc_req=broadcast_required(target, passive_predicates[i]);
      if(passive_broadcast_only || bc_req)
      {
        exprt new_value = passive_nondet ?
          nil_exprt() :
          (bc_req ?
            specific_abstractor->get_value(-1 /* not used */ , all_predicates, passive_predicates_wp[i], concrete_model.ns, target) :
            abstract_transition_relation.values[i]);

#ifdef DEBUG
        std::cout << "New value: ";
        if(new_value.is_constant())
        {
          std::cout << from_expr(concrete_model.ns, "", new_value);
        } else if(!new_value.is_nil()) {
          unsigned p=safe_str2unsigned(new_value.get(ID_identifier).c_str());
          std::cout << from_expr(concrete_model.ns, "", all_predicates[p]);
        } else {
          std::cout << "*";
        }
        std::cout << std::endl << std::endl;
#endif

        adjust_pred_index(new_value, all_predicates, passive_predicates);
        concurrency_aware_abstract_transition_relation->passive_values[i]=new_value;

        // if it changes, it's output
        // TODO never used!?
        // concurrency_aware_abstract_transition_relation->to_passive_predicates.insert(i);

      }
    }
       
    if(passive_broadcast_only && 
        abstract_transition_relation.values.find(i)!=abstract_transition_relation.values.end())
    {
      abstract_transition_relation.values[i]=exprt(ID_predicate_symbol, typet(ID_bool));
      abstract_transition_relation.values[i].set(ID_identifier, i);
    }
  }
}

void concurrency_aware_abstractort::abstract_expression(
    const predicatest &predicates,
    exprt &expr,
    const namespacet &ns,
    goto_programt::const_targett program_location)
{
  this->specific_abstractor->abstract_expression(predicates, expr, ns, program_location);
}

void concurrency_aware_abstractort::abstract_assume_guard(
    const predicatest &predicates,
    exprt &expr,
    const namespacet &ns,
    goto_programt::const_targett program_location)
{
  this->specific_abstractor->abstract_assume_guard(predicates, expr, ns, program_location);
}



/*******************************************************************\

Function: concurrency_aware_abstractor::targets_of_lvalue

Inputs:

Outputs:

Purpose: compute possible targets of lvalue

\*******************************************************************/

std::set<symbol_exprt> concurrency_aware_abstractort::targets_of_lvalue(const exprt& lvalue, goto_programt::const_targett program_location)
{

  std::set<symbol_exprt> result;
  if(lvalue.id() == ID_index)
  {
    exprt array_name = lvalue.op0();
    if(array_name.id() == ID_symbol)
    {
      result.insert(to_symbol_expr(array_name));
    } else {
      return targets_of_lvalue(array_name, program_location);
    }
  } else if(lvalue.id() == ID_member) {
    assert(lvalue.operands().size() == 1);
    return targets_of_lvalue(lvalue.op0(), program_location);
  } else if(lvalue.id() == ID_symbol) {
    result.insert(to_symbol_expr(lvalue));
  } else if(lvalue.id() == ID_dereference) {
    // We would like to add anything the pointer can point to,
    // but not the pointer itself

    value_setst::valuest value_set;
    pointer_info.get_values(program_location, lvalue.op0(), value_set);
    for(value_setst::valuest::iterator it = value_set.begin(); it != value_set.end(); it++)
    {
      if(it->id() != ID_object_descriptor)
      {
        // TODO: We may need to deal with this situation more carefully
        continue;
      }
      object_descriptor_exprt& object_descriptor = to_object_descriptor_expr(*it);
      if(object_descriptor.offset() != from_integer(0, index_type()))
      {
        std::cout << "Pointer " << from_expr(lvalue.op0()) << " can point to " << from_expr(*it) << " at line " <<
          program_location->location.get_line() << ", we cannot handle this" << std::endl;
        exit(1);
      }

      if(object_descriptor.object().id() != ID_symbol)
      {
        std::cout << "Pointer " << from_expr(lvalue.op0()) << " can point to " << from_expr(*it) << " at line " <<
          program_location->location.get_line() << ", we cannot handle this" << std::endl;
        exit(1);
      }

      result.insert(to_symbol_expr(object_descriptor.object()));
    }

  } else {
    std::cout << "Cannot currently handle lvalue: " << from_expr(lvalue) << std::endl;
    assert(false);
  }
  return result;
}



bool concurrency_aware_abstractort::broadcast_required(
    goto_programt::const_targett target,
    const predicatet &predicate)
{
  // Get targets of assignment
  std::set<symbol_exprt> targets = targets_of_lvalue(target->code.op0(), target);
  std::set<symbol_exprt> locations = locations_of_expression(predicate, target, pointer_info, concrete_model.ns);
#ifdef DEBUG_BROADCAST
  std::cout << "Targets of lvalue " << from_expr(concrete_model.ns, "", target->code.op0()) << ":" << std::endl;
  for(std::set<symbol_exprt>::iterator it = targets.begin(); it != targets.end(); it++)
  {
    std::cout << "  " << from_expr(concrete_model.ns, "", *it) << " -- ";
    if(is_global(concrete_model.ns.lookup(it->get(ID_identifier))))
    {
      std::cout << "SHARED";
    } else {
      assert(is_procedure_local(concrete_model.ns.lookup(it->get(ID_identifier))));
      std::cout << "LOCAL";
    }
    std::cout << std::endl;
  }
  std::cout << "Locations of predicate " << from_expr(concrete_model.ns, "", predicate) << ":" << std::endl;
  for(std::set<symbol_exprt>::iterator it = locations.begin(); it != locations.end(); it++)
  {
    std::cout << "  " << from_expr(concrete_model.ns, "", *it) << " -- ";
    if(is_global(concrete_model.ns.lookup(it->get(ID_identifier))))
    {
      std::cout << "SHARED";
    } else {
      assert(is_procedure_local(concrete_model.ns.lookup(it->get(ID_identifier))));
      std::cout << "LOCAL";
    }
    std::cout << std::endl;
  }
#endif

  std::set<symbol_exprt> intersection_of_targets_and_locations;

  std::set_intersection(targets.begin(), targets.end(), locations.begin(), locations.end(),
      std::insert_iterator<std::set<symbol_exprt> >(intersection_of_targets_and_locations,intersection_of_targets_and_locations.begin()) );
#ifdef DEBUG_BROADCAST
  std::cout << "Intersection:" << std::endl;
  for(std::set<symbol_exprt>::iterator it = intersection_of_targets_and_locations.begin(); it != intersection_of_targets_and_locations.end(); it++)
  {
    std::cout << "  " << from_expr(concrete_model.ns, "", *it) << " -- ";
    if(is_global(concrete_model.ns.lookup(it->get(ID_identifier))))
    {
      std::cout << "SHARED";
    } else {
      assert(is_procedure_local(concrete_model.ns.lookup(it->get(ID_identifier))));
      std::cout << "LOCAL";
    }
    std::cout << std::endl;
  }
#endif

  bool require_broadcast = false;
  for(std::set<symbol_exprt>::iterator
      it=intersection_of_targets_and_locations.begin();
      !require_broadcast && it!=intersection_of_targets_and_locations.end();
      it++)
    require_broadcast = concrete_model.ns.lookup(it->get(ID_identifier)).is_shared();

  if(require_broadcast)
  {
#ifdef DEBUG_BROADCAST
    std::cout << "BROADCAST REQUIRED: predicate and l-value intersect on shared location" << std::endl;
#endif
    return true;


  } else {
#ifdef DEBUG_BROADCAST
    std::cout << "Predicate and l-value do not intersect on shared location, so no broadcast required" << std::endl;
#endif
  }

#ifdef DEBUG_BROADCAST
  std::cout << std::endl;
#endif

  return false;

}
