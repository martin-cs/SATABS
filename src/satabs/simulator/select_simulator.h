/*******************************************************************\

Module: Simulator Selection

Authors: Daniel Kroening, kroening@kroening.com
Karen Yorav

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_SELECT_SIMULATOR_H
#define CPROVER_CEGAR_SELECT_SIMULATOR_H

#include "../loop_component.h"

class contextt;
class optionst;
class simulatort;

simulatort *select_simulator(
  const optionst &options,
  const loop_componentt::argst &args,
  contextt &_shadow_context);

#endif
