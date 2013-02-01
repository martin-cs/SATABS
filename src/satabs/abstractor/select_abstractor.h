/*******************************************************************\

Module: Abstractor Selection

Authors: Daniel Kroening, kroening@kroening.com
Karen Yorav

Date: September 2005

\*******************************************************************/

#ifndef CPROVER_CEGAR_SELECT_ABSTRACTOR_H
#define CPROVER_CEGAR_SELECT_ABSTRACTOR_H

#include <goto-programs/goto_functions.h>

#include "../loop_component.h"

class abstractort;
class optionst;

abstractort *select_abstractor(
  const optionst &options,
  const loop_componentt::argst &args);

#endif
