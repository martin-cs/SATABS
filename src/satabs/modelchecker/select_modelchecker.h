/*******************************************************************\

Module: Model Checker Selection

Authors: Daniel Kroening, kroening@kroening.com
Karen Yorav

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_SELECT_MODELCHECKER_H
#define CPROVER_CEGAR_SELECT_MODELCHECKER_H

#include "../loop_component.h"

class optionst;
class modelcheckert;

modelcheckert *select_modelchecker(
    const optionst &options,
    const loop_componentt::argst &args);

#endif
