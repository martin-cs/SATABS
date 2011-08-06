/*
 * locations_of_expressions.cpp
 *
 *  Created on: Aug 2, 2011
 *      Author: alad
 */

#include "locations_of_expressions.h"

#include <ansi-c/c_types.h>
#include <util/arith_tools.h>

bool locations_intersect(const predicatet& phi, const predicatet& psi, const goto_programt::const_targett program_location, value_set_analysist& pointer_info, const namespacet& ns)
{
	std::set<symbol_exprt> locations_phi = locations_of_expression(phi, program_location, pointer_info, ns);
	std::set<symbol_exprt> locations_psi = locations_of_expression(psi, program_location, pointer_info, ns);
	std::set<symbol_exprt> intersection;
    std::set_intersection(locations_phi.begin(), locations_phi.end(), locations_psi.begin(), locations_psi.end(),
              std::insert_iterator<std::set<symbol_exprt> >(intersection,intersection.begin()) );
    return !intersection.empty();
}

std::set<symbol_exprt> locations_of_expression(const predicatet& phi, const goto_programt::const_targett program_location, value_set_analysist& pointer_info, const namespacet& ns)
{
#ifdef DEBUG
	std::cout << "Computing locations of " << from_expr(ns, "", phi) << std::endl;
#endif
	return locations_of_expression_rec(phi, program_location, pointer_info, ns);

}



std::set<symbol_exprt> locations_of_expression_rec(const predicatet& phi, const goto_programt::const_targett program_location, value_set_analysist& pointer_info, const namespacet& ns)
{
	if(phi.id()==ID_address_of)
	{
		// Addresses are constant -- don't need to read the symbol whose address we are taking
		return std::set<symbol_exprt>();
	}

	if(phi.id()==ID_constant)
	{
		// No symbols associated with a constant
		return std::set<symbol_exprt>();
	}

	if(phi.id()==ID_symbol)
	{
		std::set<symbol_exprt> result;
		result.insert(to_symbol_expr(phi));
		return result;
	}

	if(phi.id()==ID_dereference)
	{
		// We would like to add the pointer itself (which for now we require to be a variable)
		// and anything it can point to

		std::set<symbol_exprt> result;

		result = locations_of_expression_rec(phi.op0(), program_location, pointer_info, ns); // if we have *p, we insert the locations of p itself

		value_setst::valuest value_set;
		pointer_info.get_values(program_location, phi.op0(), value_set);

		for(value_setst::valuest::iterator it = value_set.begin(); it != value_set.end(); it++)
		{
			if(it->id() != ID_object_descriptor)
			{
				// TODO: We may need to deal with this situation more carefully
				continue;
			}

			object_descriptor_exprt& object_descriptor = to_object_descriptor_expr(*it);

			if(object_descriptor.object().id() == "NULL-object")
			{
				// No locations associated with NULL
				continue;
			}

			if(object_descriptor.offset() != from_integer(0, index_type()))
			{
				std::cout << "(*) Warning: pointer " << from_expr(ns, "", phi.op0()) << " can point to " << from_expr(ns, "", *it) << " at " <<
						program_location->location << ", this needs further investigation" << std::endl;
				continue;
			}

			if(object_descriptor.object().id() != ID_symbol)
			{
				std::cout << "(**) Warning: pointer " << from_expr(ns, "", phi.op0()) << " can point to " << from_expr(ns, "", *it) << " at " <<
						program_location->location << ", this needs further investigation" << std::endl;
				continue;
			}

			result.insert(to_symbol_expr(object_descriptor.object()));
		}

		return result;
	}

	if(phi.id()=="invalid-pointer" || phi.id()=="pointer_arithmetic" || phi.id()=="pointer_difference")
	{
		std::cout << "(***) Warning: cannot yet handle " << from_expr(ns, "", phi) << ", ignoring it" << std::endl;
		return std::set<symbol_exprt>();
	}


	{
		/* Default case: iterate through the operands of the expression, adding all locations referenced therein */
		std::set<symbol_exprt> result;
		for(unsigned int i = 0; i < phi.operands().size(); i++)
		{
			std::set<symbol_exprt> symbols_i = locations_of_expression_rec(phi.operands()[i], program_location, pointer_info, ns);
			for(std::set<symbol_exprt>::iterator it = symbols_i.begin(); it != symbols_i.end(); it++)
			{
				result.insert(*it);
			}
		}
		return result;
	}

}
