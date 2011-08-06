/*
 * concurrency_aware_abstractor.cpp
 *
 *  Created on: Aug 2, 2011
 *      Author: alad
 */

#include "concurrency_aware_abstractor.h"

#include "concurrency_aware_abstract_transition_relation.h"

#include "locations_of_expressions.h"

#include "predabs_aux.h"

#include <ansi-c/c_types.h>

#include <util/arith_tools.h>

#include <sstream>


void concurrency_aware_abstractort::pred_abstract_block(
			goto_programt::const_targett target,
			const predicatest &predicates,
			abstract_transition_relationt &
			abstract_transition_relation)
{
	concurrency_aware_abstract_transition_relationt& concurrency_aware_abstract_transition_relation =
			(concurrency_aware_abstract_transition_relationt&) abstract_transition_relation;

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
		  assert(all_predicates.size() == predicates.size() + passive_predicates.size());
		  // Add passive versions of existing predicates (lookup does this)
		  if(!predicates.find(make_passive(predicates[i])))
		  {
			  passive_predicates.lookup(make_passive(predicates[i]));
			  all_predicates.lookup(make_passive(predicates[i]));
		  }
	  }


	  std::vector<exprt> passive_predicates_wp;

	  std::list<exprt> passive_constraints;

	  build_equation(
	    concrete_model.ns,
	    passive_predicates,
	    target,
	    passive_constraints,
	    passive_predicates_wp);

	  for(unsigned i=0; i<passive_predicates.size(); i++)
	  {
	    if(passive_predicates_wp[i]==passive_predicates[i])
	    {
	      concurrency_aware_abstract_transition_relation.passive_values.erase(i);
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

	      if(broadcast_required(target, passive_predicates[i], target))
	      {
	          exprt new_value = specific_abstractor->get_value(-1 /* not used */ , all_predicates, passive_predicates_wp[i], concrete_model.ns, target);

	#ifdef DEBUG
	          std::cout << "New value: ";
	          if(new_value.is_constant())
	          {
	        	  std::cout << from_expr(concrete_model.ns, "", new_value);
	          } else if(!new_value.is_nil()) {
				  unsigned p=atoi(new_value.get(ID_identifier).c_str());
				  std::cout << from_expr(concrete_model.ns, "", all_predicates[p]);
	          } else {
	        	  std::cout << "*";
	          }
	          std::cout << std::endl << std::endl;
	#endif

	          concurrency_aware_abstract_transition_relation.passive_values[i]=new_value;

	          // if it changes, it's output
	          concurrency_aware_abstract_transition_relation.to_passive_predicates.insert(i);

	      }
	    }
	  }

}




exprt concurrency_aware_abstractort::make_passive(exprt phi)
{
	// Recursively mutate the expression, to make it passive
	return make_passive_rec(phi);
}

exprt concurrency_aware_abstractort::make_passive_rec(exprt phi)
{
	if(phi.id()==ID_plus || phi.id()==ID_minus || phi.id()==ID_mult || phi.id()==ID_div
			|| phi.id()==ID_mod || phi.id()==ID_shl || phi.id()==ID_ashr || phi.id()==ID_lshr
			|| phi.id()==ID_lt || phi.id()==ID_gt || phi.id()==ID_le || phi.id()==ID_ge
			|| phi.id()==ID_notequal || phi.id()==ID_equal || phi.id()==ID_bitand
			|| phi.id()==ID_bitxor || phi.id()==ID_bitor || phi.id()==ID_and || phi.id()==ID_or
			|| phi.id()==ID_implies)

	  {
		for(unsigned int i = 0; i < phi.operands().size(); i++)
		{
			phi.operands()[i] = make_passive_rec(phi.operands()[i]);
		}
		return phi;
	  }

	  else if(phi.id()==ID_unary_minus || phi.id()==ID_unary_plus || phi.id()==ID_not || phi.id()==ID_bitnot)
	  {
		  assert(phi.operands().size() == 1);
		  phi.op0() = make_passive_rec(phi.op0());
		  return phi;
	  }

	  else if(phi.id()=="invalid-pointer")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="pointer_arithmetic")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="pointer_difference")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="NULL-object")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()==ID_integer_address ||
			  phi.id()==ID_stack_object ||
			  phi.id()==ID_static_object)
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()==ID_infinity)
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="builtin-function")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="pointer_object")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="object_value")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="pointer_object_has_type")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()==ID_array_of)
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()==ID_pointer_offset)
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="pointer_base")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="pointer_cons")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="same-object")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="dynamic_object")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="is_dynamic_object")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="is_zero_string")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="zero_string")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="zero_string_length")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()=="buffer_size")
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()==ID_pointer_offset)
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()==ID_isnan)
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()==ID_isfinite)
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()==ID_isinf)
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()==ID_isnormal)
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()==ID_builtin_offsetof)
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()==ID_builtin_alignof)
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()==ID_address_of)
	  {
		  phi.op0() = make_passive_rec(phi.op0());
		  return phi;
	  }

	  else if(phi.id()==ID_dereference)
	  {
		  phi.op0() = make_passive_rec(phi.op0());
		  return phi;
	  }

	  else if(phi.id()==ID_index) {
		  assert(phi.operands().size() == 2);
		  phi.op0() = make_passive_rec(phi.op0());
		  phi.op1() = make_passive_rec(phi.op1());
		  return phi;
	  }

	  else if(phi.id()==ID_member)
	  {
		  /* Somewhat surprisingly, a member expression has one operand - the containing struct.
		   * Presumably the field is specified explicitly.
		   */
		  assert(phi.operands().size() == 1);
		  phi.op0() = make_passive_rec(phi.op0());
		  return phi;
	  }

	  else if(phi.id()=="array-member-value")
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()=="struct-member-value")
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_sideeffect)
	  {
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }
	  }

	  else if(phi.id()==ID_ieee_float_equal)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_width)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_ieee_float_notequal)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_byte_update_little_endian)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_byte_update_big_endian)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_abs)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_if)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_forall)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_exists)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()=="lambda")
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_with)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_symbol)
	  {
		  if(is_procedure_local(concrete_model.ns.lookup(phi.get(ID_identifier))))
		  {
			  std::ostringstream stream;
			  stream << phi.get(ID_identifier) << "$";
			  phi.set(ID_identifier, stream.str());
		  }
		  return phi;
	  }

	  else if(phi.id()==ID_next_symbol)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_nondet_symbol)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()=="predicate_symbol")
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()=="predicate_next_symbol")
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()=="quantified_symbol")
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()=="nondet_bool")
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()=="object_descriptor")
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()=="Hoare")
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_code)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_constant)
		return phi;

	  else if(phi.id()==ID_string_constant)
		return phi;

	  else if(phi.id()==ID_struct)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_vector)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_union)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_array)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()=="array-list")
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_typecast)
		  {
			  phi.op0() = make_passive_rec(phi.op0());
			  return phi;
		  }

	  else if(phi.id()=="implicit_address_of")
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()=="implicit_dereference")
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_comma)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_cond)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(std::string(phi.id_string(), 0, 9)=="overflow-")
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_unknown)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()=="invalid")
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_extractbit)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_initializer_list)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	  else if(phi.id()==ID_designated_initializer)
		  { std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	{ std::cout << "Cannot yet handle " << from_expr(concrete_model.ns, "", phi) << std::endl; assert(false); throw "not yet supported"; }

	return phi;
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
		  const predicatet &predicate,
		  goto_programt::const_targett program_location)
{
  	// Get targets of assignment
  	std::set<symbol_exprt> targets = targets_of_lvalue(target->code.op0(), target);
  	std::set<symbol_exprt> locations = locations_of_expression(predicate, program_location, pointer_info, concrete_model.ns);
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
  	for(std::set<symbol_exprt>::iterator it = intersection_of_targets_and_locations.begin(); it != intersection_of_targets_and_locations.end(); it++)
  	{
  		if(is_global(concrete_model.ns.lookup(it->get(ID_identifier))))
  		{
  			require_broadcast = true;
  			break;
  		}
  	}

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
