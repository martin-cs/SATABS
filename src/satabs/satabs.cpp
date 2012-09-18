/*******************************************************************\

Module: CEGAR Main Module 

Authors: Daniel Kroening, kroening@kroening.com
         Karen Yorav

Date: June 2003

\*******************************************************************/

/*

   SATABS
   Counterexample Guided Abstraction Refinement for ANSI-C
   Copyright (C) 2003-2008 Daniel Kroening <kroening@kroening.com>

Purpose: Main Module

*/

#include <unicode.h>

#include "cmdline_options.h"

#ifndef _WIN32

#include <cstdlib>
#include <signal.h>
#include <iostream>

void xcpu_termination_handler(int signum)
{
  std::cout << std::endl << "TIME LIMIT EXCEEDED" << std::endl;
  exit(0);
}

#endif

/*******************************************************************\

Function: main

Inputs:

Outputs:

Purpose:

\*******************************************************************/

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  const char **argv=narrow_argv(argc, argv_wide);
  cmdline_optionst cmdline_options(argc, argv); 
  return cmdline_options.main();
}
#else
int main(int argc, const char **argv) 
{
  #ifndef _WIN32
  signal(SIGXCPU, &xcpu_termination_handler);
  #endif

  cmdline_optionst cmdline_options(argc, argv); 
  return cmdline_options.main();
}
#endif
