/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <solvers/sat/satcheck.h>

#include "simulator_base.h"

/*******************************************************************\

Function: simulator_baset::is_satisfiable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simulator_baset::is_satisfiable(formulat formula)
{
  satcheckt satcheck;

  #ifdef DEBUG  
  std::cout << "simulator_baset::is_satisfiable1\n";
  std::cout << "F: " << formula << std::endl;
  #endif

  formula_container.reset_prop();  

  #ifdef DEBUG
  std::cout << "simulator_baset::is_satisfiable2\n";
  #endif

  literalt l=formula.convert(satcheck);
  satcheck.l_set_to(l, true);
  
  return is_satisfiable(satcheck);
}

/*******************************************************************\

Function: simulator_baset::is_satisfiable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simulator_baset::is_satisfiable(cnf_solvert &solver)
{
  std::cout << "Running " << solver.solver_text() << ", "
            << solver.no_variables() << " variables, "
            << solver.no_clauses() << " clauses" << std::endl;
  
  switch(solver.prop_solve())
  {
  case propt::P_SATISFIABLE:
    return true;
    
  case propt::P_UNSATISFIABLE:
    return false;
    
  default:
    assert(false);
  }
  
  return false;
}
