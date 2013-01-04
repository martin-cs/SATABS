/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <cassert>
#include <iostream>

#include "bp_util.h"

/*******************************************************************\

Function: vector_width

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned vector_width(const typet &type)
{
  if(type.id()==ID_empty)
    return 0;
  else if(type.id()==ID_bool)
    return 1;
  else if(type.id()=="bool-vector")
    return atoi(type.get(ID_width).c_str());
  else
  {
    std::cerr << "unexpected vector type: "
              << type.pretty() << std::endl;
    assert(false);
  }
}
