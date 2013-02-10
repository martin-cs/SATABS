/*******************************************************************\

Module: Simulator Selection

Authors: Daniel Kroening, kroening@kroening.com
Karen Yorav

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_SELECT_SIMULATOR_H
#define CPROVER_CEGAR_SELECT_SIMULATOR_H

#include "../loop_component.h"

class symbol_tablet;
class optionst;
class simulatort;

simulatort *select_simulator(
  const optionst &options,
  symbol_tablet &_shadow_symbol_table);

#endif
