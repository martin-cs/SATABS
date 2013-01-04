/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "partial_order_sat.h"
#include "partial_order_solver.h"

/*******************************************************************\

Function: partial_order_satt::partial_order_satt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

partial_order_satt::partial_order_satt():
  satcheck_zchaff_baset(solver_ptr=new partial_order_solvert)
{
}

/*******************************************************************\

Function: partial_order_satt::~partial_order_satt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

partial_order_satt::~partial_order_satt()
{
  delete solver_ptr;
}
