/*******************************************************************\

Module: Refiner Selection

Authors: Daniel Kroening, kroening@cs.cmu.edu
Karen Yorav

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_SATABS_SELECT_REFINER_H
#define CPROVER_SATABS_SELECT_REFINER_H

#include "../loop_component.h"

class optionst;
class refinert;

refinert *select_refiner(
    const optionst &options,
    const loop_componentt::argst &args);

#endif
