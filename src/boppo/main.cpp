/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/*

  BOPPO
  Boolean Programs with Partial Order Reduction
  Copyright (C) 2003-2004 Daniel Kroening <kroening@kroening.com>

*/

#include "parseoptions.h"

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char **argv)
{
  boppo_parseoptionst boppo_parseoptions(argc, argv);
  return boppo_parseoptions.main();
}
