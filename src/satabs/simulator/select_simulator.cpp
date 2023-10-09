/*******************************************************************\

Module: simulator Selection

Authors: Daniel Kroening, kroening@kroening.com
Karen Yorav

Date: June 2003

\*******************************************************************/

#include <util/options.h>

#include "select_simulator.h"
#include "simulator_path_symex.h"
#include "simulator_loop_detection.h"

/*******************************************************************\

Function: select_simulator

Inputs:

Outputs:

Purpose:

\*******************************************************************/

simulatort *select_simulator(
  const optionst &options,
  symbol_tablet &_shadow_symbol_table)
{
  const std::string name=options.get_option("simulator");

  if(name=="sat")
  {
    if(options.get_bool_option("loop-detection"))
      return new simulator_loop_detectiont(options, _shadow_symbol_table);

    return new simulator_path_symext(options);
    //return new simulator_symext(options);
  }
  else
    throw "unknown simulator: "+name;
}
