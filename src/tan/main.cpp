/*******************************************************************\

Module: Main Module

Author: CM Wintersteiger

\*******************************************************************/

#include <signal.h>

#include <iostream>
#include <cstdlib>

#include "tan_parse_options.h"

void xcpu_termination_handler(int signum)
{
  std::cout << std::endl << "TIME LIMIT EXCEEDED" << std::endl;
  exit(0);
}

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char **argv)
{
  #ifndef _WIN32
  signal(SIGXCPU, &xcpu_termination_handler);
  #endif

  try
  {
    tan_parse_optionst parse_options(argc, argv);
    return parse_options.main();
  }

  catch (const char* e)
  {
    std::cout << std::endl << "Caught exception: " << e << std::endl;
  }

  catch (const std::string &s)
  {
    std::cout << std::endl << "Caught exception: " << s << std::endl;
  }

  catch (const std::bad_alloc &e)
  {
    std::cout << std::endl << "MEMORY LIMIT EXCEEDED" << std::endl;
  }
}
