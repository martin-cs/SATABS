/*******************************************************************\

Module: Cartesian Abstractor (generates abstract program given a set
of predicates, using cartesian approximation)

Author: Alastair Donaldson

Date: April 2010

\*******************************************************************/

#include <algorithm>
#include <iterator>

#include <ansi-c/c_types.h>
#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>
#include <arith_tools.h>
#include <simplify_expr.h>

#include "check_redundancy.h"
#include "abstractor_wp_cartesian.h"
#include "locations_of_expressions.h"
#include "../prepare/concrete_model.h"

abstractor_wp_cartesiant::abstractor_wp_cartesiant(
  const argst &args,
  const unsigned int max_cube_length):
  abstractor_wpt(args),
  max_cube_length(max_cube_length),
  pointer_info(args.concrete_model.ns)
{
  status("Performing pointer analysis for Cartesian abstraction");
  pointer_info(args.concrete_model.goto_functions);
  status("Pointer analysis complete");
}

exprt abstractor_wp_cartesiant::get_value(
    unsigned p_nr,
    const predicatest &predicates,
    const exprt &value,
    const namespacet& ns,
    goto_programt::const_targett program_location
    )
{

  exprt new_value = abstractor_wpt::get_value(p_nr, predicates, value, ns, program_location);

#ifdef DEBUG
  std::cout << "New value: ";
  if(new_value.is_constant())
  {
    std::cout << from_expr(concrete_model.ns, "", new_value);
  } else if(!new_value.is_nil())
  {
    unsigned p=atoi(new_value.get(ID_identifier).c_str());
    std::cout << from_expr(concrete_model.ns, "", predicates[p]);
  } else {
    std::cout << "*";
  }
  std::cout << std::endl << std::endl;
#endif

  /* If we find the new value is a constant, or another predicate,
   * just return it
   */
  if(!new_value.is_nil())
  {
    return new_value;
  }

  /* We couldn't work out a good new value easily, so we will apply
   * the cartesian approximation, and find the best approximation
   * for 'value' using disjunctions of cubes over our predicates,
   * considering cubes up to length 'max_cube_length'
   */

#ifdef DEBUG
  std::cout << "Starting cube enumeration, bounded by " << max_cube_length << std::endl;
#endif

  exprt not_value = not_exprt(value);

  std::set<cubet> implies_value = compute_largest_disjunction_of_cubes(predicates, value, not_value, program_location);
  std::set<cubet> implies_not_value = compute_largest_disjunction_of_cubes(predicates, not_value, value, program_location);

#ifdef DEBUG
  std::cout << "Relevant cubes that imply " << from_expr(concrete_model.ns, "", not_value) << ":" << std::endl;
  for(std::set<cubet>::iterator it = implies_not_value.begin(); it != implies_not_value.end(); it++)
  {
    std::cout << "  " << from_expr(concrete_model.ns, "", cube_to_expr(*it)) << std::endl;
  }
  std::cout << "Relevant cubes that imply " << from_expr(concrete_model.ns, "", value) << ":" << std::endl;
  for(std::set<cubet>::iterator it = implies_value.begin(); it != implies_value.end(); it++)
  {
    std::cout << "  " << from_expr(concrete_model.ns, "", cube_to_expr(*it)) << std::endl;
  }
  std::cout << std::endl;
#endif

  exprt true_condition = disjunction_of_cubes_using_predicate_variables(implies_value, predicates);
  exprt false_condition = disjunction_of_cubes_using_predicate_variables(implies_not_value, predicates);

  if(true_condition == false_exprt() && false_condition == false_exprt())
  {
    return exprt(ID_nondet_bool);
  }

  if(true_condition == false_exprt())
  {
    return and_exprt(not_exprt(false_condition), exprt(ID_nondet_bool));
  }

  if(false_condition == false_exprt())
  {
    return or_exprt(true_condition, exprt(ID_nondet_bool));
  }

  return or_exprt(true_condition, and_exprt(not_exprt(false_condition), exprt(ID_nondet_bool)));

}


exprt abstractor_wp_cartesiant::cube_to_expr(const cubet& cube)
{
  bool first = true;
  exprt cube_conjunction = false_exprt();
  for(cubet::iterator it = cube.begin(); it != cube.end(); it++)
    if(first)
    {
      first = false;
      cube_conjunction = *it;
    } else {
      cube_conjunction = and_exprt(cube_conjunction, *it);
    }
  return cube_conjunction;
}

static int find_in_predicates(const predicatest& predicates, const predicatet& phi)
{
  for(unsigned int i = 0; i < predicates.size(); i++)
  {
    if(predicates[i] == phi)
    {
      return i;
    }
  }
  return -1;
}

exprt abstractor_wp_cartesiant::disjunction_of_cubes_using_predicate_variables(const std::set<cubet>& cubes, const predicatest& predicates)
{
  /* If there are no cubes, then the only cube implying the predicate is 'false' */
  exprt result = false_exprt();

  bool first_outer = true;

  for(std::set<cubet>::const_iterator it = cubes.begin(); it != cubes.end(); it++)
  {
    assert(!it->empty());
    exprt cube_over_booleans;
    bool first_inner = true;
    for(cubet::const_iterator it2 = it->begin(); it2 != it->end(); it2++)
    {
      exprt literal;
      int index = find_in_predicates(predicates, *it2);
      if(-1 != index)
      {
        literal = exprt(ID_predicate_symbol, typet(ID_bool));
        literal.set(ID_identifier, index);
      } else {
        assert(it2->id() == ID_not);
        index = find_in_predicates(predicates, it2->op0());
        assert(-1 != index);
        literal = exprt(ID_predicate_symbol, typet(ID_bool));
        literal.set(ID_identifier, index);
        literal = not_exprt(literal);
      }

      if(first_inner)
      {
        first_inner = false;
        cube_over_booleans = literal;
      } else {
        cube_over_booleans = and_exprt(cube_over_booleans, literal);
      }
    }

    if(first_outer)
    {
      first_outer = false;
      result = cube_over_booleans;
    } else {
      result = or_exprt(result, cube_over_booleans);
    }

  }

  return result;
}

std::set<abstractor_wp_cartesiant::cubet> abstractor_wp_cartesiant::compute_largest_disjunction_of_cubes(
    const predicatest& predicates,
    const predicatet& phi,
    const predicatet& not_phi,
    goto_programt::const_targett program_location)
{
  std::set<cubet> implies_phi; /* The result we will compute */
  std::set<cubet> implies_not_phi;

  if(0 == max_cube_length)
  {
    return implies_phi;
  }

  std::list<cubet> queue;
  for(unsigned int i = 0; i < predicates.size(); i++)
  {
    if(locations_intersect(phi, predicates[i], program_location, pointer_info, concrete_model.ns))
    {
      cubet initial_cube;
      initial_cube.insert(predicates[i]);
#ifdef DEBUG
      std::cout << "Considering initial cube: " << from_expr(concrete_model.ns, "", cube_to_expr(initial_cube)) << std::endl;
#endif
      if(cube_is_satisfiable(initial_cube))
      {
#ifdef DEBUG
        std::cout << "   it is satisfiable." << std::endl;
#endif
        queue.push_back(initial_cube);
      } else {
#ifdef DEBUG
        std::cout << "   it is not satisfiable." << std::endl;
#endif
      }

      cubet initial_cube_negated;
      initial_cube_negated.insert(not_exprt(predicates[i]));
#ifdef DEBUG
      std::cout << "Considering initial cube: " << from_expr(concrete_model.ns, "", cube_to_expr(initial_cube_negated)) << std::endl;
#endif
      if(cube_is_satisfiable(initial_cube_negated))
      {
#ifdef DEBUG
        std::cout << "   it is satisfiable." << std::endl;
#endif
        queue.push_back(initial_cube_negated);
      } else {
#ifdef DEBUG
        std::cout << "   it is not satisfiable." << std::endl;
#endif
      }
    }
  }

  std::set<cubet> cubes_tried;

  while(!queue.empty())
  {
    cubet current_cube = queue.front();

    queue.pop_front();

#ifdef DEBUG
    std::cout << "Considering cube: " << from_expr(concrete_model.ns, "", cube_to_expr(current_cube)) << std::endl;
#endif

    cubes_tried.insert(current_cube);

    assert(cube_is_satisfiable(current_cube));

#ifdef DEBUG
    std::cout << "It is satisfiable." << std::endl;
#endif

    if(contains_subcube(implies_phi, current_cube) || contains_subcube(implies_not_phi, current_cube))
    {
#ifdef DEBUG
      std::cout << "It is subsumed." << std::endl;
#endif
      continue;
    }

    if(implies(current_cube, phi))
    {
#ifdef DEBUG
      std::cout << "It implies " << from_expr(concrete_model.ns, "", phi) << std::endl;
#endif
      implies_phi.insert(current_cube);
    } else if(implies(current_cube, not_phi)) {
#ifdef DEBUG
      std::cout << "It implies " << from_expr(concrete_model.ns, "", not_phi) << std::endl;
#endif
      implies_not_phi.insert(current_cube);
    }
#ifdef DEBUG
    else {
      std::cout << "It neither implies " << from_expr(concrete_model.ns, "", phi) << " nor " << from_expr(concrete_model.ns, "", not_phi) << std::endl;
    }

#endif

    if(current_cube.size() >= max_cube_length)
    {
      // Only try cubes up to a certain length
      continue;
    }

    if((implies_phi.end() != implies_phi.find(current_cube)) || (implies_not_phi.end() != implies_not_phi.find(current_cube)))
    {
      // Don't try larger cubes if this is a prime implicant, or if larger cubes cannot imply phi
      continue;
    }

    for(unsigned int i = 0; i < predicates.size(); i++)
    {
      if(!(predicate_locations_intersects_cube_locations(predicates[i], current_cube, program_location)))
      {
        // No point extending the cube with a predicate that shares locations - it will not
        // tell us anything stronger (unless it makes the cube unsatisfiable)
        continue;
      }

      cubet cube_extended_with_predicate_i = current_cube;
      cubet cube_extended_with_not_predicate_i = current_cube;
      cube_extended_with_predicate_i.insert(predicates[i]);
      cube_extended_with_not_predicate_i.insert(not_exprt(predicates[i]));

      if(
          cubes_tried.end() == cubes_tried.find(cube_extended_with_predicate_i) &&
          queue.end() == std::find(queue.begin(), queue.end(), cube_extended_with_predicate_i) &&
          cube_is_satisfiable(cube_extended_with_predicate_i)
        )
      {
        queue.push_back(cube_extended_with_predicate_i);
      }

      if(
          cubes_tried.end() == cubes_tried.find(cube_extended_with_not_predicate_i) &&
          queue.end() == std::find(queue.begin(), queue.end(), cube_extended_with_not_predicate_i) &&
          cube_is_satisfiable(cube_extended_with_not_predicate_i)
        )
      {
        queue.push_back(cube_extended_with_not_predicate_i);
      }
    }
  }

  return implies_phi;

}

bool abstractor_wp_cartesiant::cube_is_satisfiable(const cubet& cube)
{
  std::map<cubet, bool>::iterator cache_entry = sat_cache.find(cube);
  if(sat_cache.end() != cache_entry) {
    return cache_entry->second;
  }

  exprt cube_conjunction = cube_to_expr(cube);

  satcheckt satcheck;
  bv_pointerst solver(concrete_model.ns, satcheck);
  solver.set_to_true(cube_conjunction);

  switch(solver.dec_solve())
  {
    case decision_proceduret::D_UNSATISFIABLE:
      sat_cache[cube] = false;
      return false;

    case decision_proceduret::D_SATISFIABLE:
      sat_cache[cube] = true;
      return true;

    default:
      throw "unexpected result from dec_solve()";
  }

  return false;
}

bool abstractor_wp_cartesiant::predicate_locations_intersects_cube_locations(
    const predicatet& phi,
    const cubet& cube,
    goto_programt::const_targett program_location)
{
  for(cubet::const_iterator it = cube.begin(); it != cube.end(); it++)
  {
    if(locations_intersect(phi, *it, program_location, pointer_info, concrete_model.ns))
    {
      return true;
    }
  }
  return false;
}

bool abstractor_wp_cartesiant::implies(const cubet& cube, const predicatet& phi)
{
#ifdef DEBUG
  std::cout << "Checking whether " << from_expr(concrete_model.ns, "", cube_to_expr(cube)) << " => " << from_expr(concrete_model.ns, "", phi) << " is valid." << std::endl;
#endif

  std::map<std::pair<cubet, predicatet>, bool>::iterator cache_entry =
    implies_cache.find(std::pair<cubet, predicatet>(cube, phi));
  if(implies_cache.end() != cache_entry) {
#ifdef DEBUG
    std::cout << "Cache says: " << cache_entry->second << std::endl;
#endif
    return cache_entry->second;
  }

  exprt cube_conjunction = cube_to_expr(cube);
  implies_exprt implication = implies_exprt(cube_conjunction, phi);

  satcheckt satcheck;
  bv_pointerst solver(concrete_model.ns, satcheck);
  solver.set_to_false(implication);

  switch(solver.dec_solve())
  {
    case decision_proceduret::D_UNSATISFIABLE:
      implies_cache[std::pair<cubet, predicatet>(cube, phi)] = true;
      return true;

    case decision_proceduret::D_SATISFIABLE:
      implies_cache[std::pair<cubet, predicatet>(cube, phi)] = false;
      return false;

    default:
      throw "unexpected result from dec_solve()";
  }

  return false;
}

bool abstractor_wp_cartesiant::contains_subcube(std::set<cubet> cube_set, cubet cube)
{
  for(std::set<cubet>::iterator it = cube_set.begin(); it != cube_set.end(); it++)
  {
    cubet intersection;

    cubet current_cube = *it;

    std::set_intersection(current_cube.begin(), current_cube.end(), cube.begin(), cube.end(),
        std::insert_iterator<cubet>(intersection,intersection.begin()) );
    if(current_cube == intersection)
    {
      return true;
    }

  }
  return false;
}

void abstractor_wp_cartesiant::abstract_expression(
    const predicatest &predicates,
    exprt &expr,
    const namespacet &ns,
    goto_programt::const_targett program_location)
{
  // Do cube enumeration
  exprt phi = expr;
  exprt not_phi = not_exprt(phi);

  // try base first
  abstractort::abstract_expression(predicates, expr, ns, program_location);
  if(expr.id()!=ID_nondet_symbol)
    return;

  if(program_location->is_assume())
  {
    // Note that we reverse phi and not_phi here, as we want F(not_phi)
    std::set<cubet> implies_not_phi = compute_largest_disjunction_of_cubes(predicates, not_phi, phi, program_location);

    exprt new_expr = not_exprt(disjunction_of_cubes_using_predicate_variables(implies_not_phi, predicates));
    expr.swap(new_expr);

    // TODO: Note: in practice, it may help to add functionality to eliminate unsatisfiable conjunctions of predicates
  }
  else
  {
    assert(program_location->is_goto() || program_location->is_assert());

    std::set<cubet> implies_phi = compute_largest_disjunction_of_cubes(predicates, phi, not_phi, program_location);
    std::set<cubet> implies_not_phi = compute_largest_disjunction_of_cubes(predicates, not_phi, phi, program_location);

    exprt true_condition = disjunction_of_cubes_using_predicate_variables(implies_phi, predicates);
    exprt false_condition = disjunction_of_cubes_using_predicate_variables(implies_not_phi, predicates);

    // a simple case first
    if(true_condition.is_false() && false_condition.is_false())
      return;

    // we would need schoose[a,b]; to avoid schoose (the bp output can't cope
    // with schoose in expressions), we use the equivalent *|a and !b|a
    and_exprt schoose(or_exprt(expr, true_condition),
        or_exprt(not_exprt(false_condition), true_condition));
    simplify(schoose, ns);
    expr.swap(schoose);
  }
}


void abstractor_wp_cartesiant::abstract_assume_guard(
    const predicatest &predicates,
    exprt &expr,
    const namespacet &ns,
    goto_programt::const_targett target)
{
  abstract_expression(predicates, expr, ns, target);
}

