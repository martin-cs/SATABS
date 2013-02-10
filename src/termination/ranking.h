/*******************************************************************\

Module: Ranking Function Synthesis

Author: CM Wintersteiger

Date: September 2008

\*******************************************************************/

#ifndef CPROVER_RANKING_H
#define CPROVER_RANKING_H

#include "ranking_body.h"

exprt ranking(
  const std::string &mode,
  const bodyt &body,
  const symbol_tablet &symbol_table,
  symbol_tablet &shadow_symbol_table,
  message_handlert &mh,
  unsigned verbosity);

#endif

