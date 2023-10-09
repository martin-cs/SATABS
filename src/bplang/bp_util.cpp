/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <iostream>

#include <util/string2int.h>

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
    return unsafe_string2unsigned(type.get_string(ID_width));
  else
  {
    std::cerr << "unexpected vector type: "
              << type.pretty() << std::endl;
    assert(false);
  }
}
