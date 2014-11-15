/*******************************************************************\

Module: Cartesian Abstractor (generates abstract program given a set
of predicates, using cartesian approximation)

Author: Alastair Donaldson

Date: April 2010

\*******************************************************************/

#ifndef CPROVER_CEGAR_ABSTRACTOR_WP_CARTESIAN_H_
#define CPROVER_CEGAR_ABSTRACTOR_WP_CARTESIAN_H_

#include <pointer-analysis/value_set_analysis.h>

#include "../prepare/concrete_model.h"
#include "abstractor_wp.h"

class abstractor_wp_cartesiant:public abstractor_wpt
{
public:
  typedef std::set<exprt> cubet;

  explicit abstractor_wp_cartesiant(
    const unsigned int max_cube_length);

protected:

  virtual exprt get_value(
    unsigned p_nr,
    const predicatest &predicates,
    const exprt &value,
    const namespacet& ns,
    goto_programt::const_targett program_location);

  virtual void abstract_expression(
    const predicatest &predicates,
    exprt &expr,
    const namespacet &ns,
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
  std::map<cubet, bool> sat_cache;
  std::map<std::pair<cubet, predicatet>, bool> implies_cache;

  value_set_analysist *pointer_info;

  virtual void set_concrete_model(const concrete_modelt &_concrete_model)
  {
    concrete_model=&_concrete_model;
    delete pointer_info;
    pointer_info=new value_set_analysist(concrete_model->ns);
    status() << "Performing pointer analysis for Cartesian abstraction" << eom;
    (*pointer_info)(concrete_model->goto_functions);
    status() << "Pointer analysis complete" << eom;
  }

};

#endif /* CPROVER_CEGAR_ABSTRACTOR_WP_CARTESIAN_H_ */
