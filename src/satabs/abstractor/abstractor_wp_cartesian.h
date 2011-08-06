/*******************************************************************\

Module: Cartesian Abstractor (generates abstract program given a set
        of predicates, using cartesian approximation)

Author: Alastair Donaldson

  Date: April 2010

\*******************************************************************/

#ifndef CPROVER_CEGAR_ABSTRACTOR_WP_CARTESIAN_H_
#define CPROVER_CEGAR_ABSTRACTOR_WP_CARTESIAN_H_

#include <pointer-analysis/value_set_analysis.h>
#include <util/std_expr.h>

#include "abstractor_wp.h"

class abstractor_wp_cartesiant:public abstractor_wpt
{
public:

	typedef std::set<exprt> cubet;

	abstractor_wp_cartesiant(const argst &args,
			                 const unsigned int max_cube_length,
			                 const goto_functionst &functions):
			                	 abstractor_wpt(args),
			                	 max_cube_length(max_cube_length),
			                	 pointer_info(args.concrete_model.ns)
	{
		status("Performing pointer analysis for Cartesian abstraction");
		pointer_info(functions);
		status("Pointer analysis complete");
	}

protected:

	virtual exprt get_value(
	    unsigned p_nr,
	    const predicatest &predicates,
	    const exprt &value,
	    const namespacet& ns,
	    goto_programt::const_targett program_location);

	virtual void abstract_assume_guard(
			  const predicatest &predicates,
			  exprt &expr,
			  const namespacet &ns,
			  goto_programt::const_targett target);

    std::set<cubet> compute_largest_disjunction_of_cubes(
    		const predicatest &predicates,
    		const exprt &value,
    		const exprt &not_value,
    		goto_programt::const_targett program_location);

    exprt cube_to_expr(const cubet& cube);

	exprt disjunction_of_cubes_using_predicate_variables(
			const std::set<cubet> &cubes,
			const predicatest &predicates);

	bool cube_is_satisfiable(const cubet& cube);

	bool implies(const cubet& cube, const predicatet& phi);

	bool predicate_locations_intersects_cube_locations(
			                 const predicatet& phi,
			                 const cubet& cube,
			                 goto_programt::const_targett program_location);

	bool contains_subcube(std::set<cubet> cube_set, cubet cube);

	const unsigned int max_cube_length;
	value_set_analysist pointer_info;
	std::map<cubet, bool> sat_cache;
	std::map<std::pair<cubet, predicatet>, bool> implies_cache;

};

#endif /* CPROVER_CEGAR_ABSTRACTOR_WP_CARTESIAN_H_ */
