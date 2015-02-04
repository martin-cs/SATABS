/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/*

  BOPPO
  Boolean Programs with Partial Order Reduction
  Copyright (C) 2003-2004 Daniel Kroening <kroening@kroening.com>

*/

#include "boppo_parse_options.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char **argv)
{
  boppo_parse_optionst boppo_parse_options(argc, argv);
  return boppo_parse_options.main();
}
