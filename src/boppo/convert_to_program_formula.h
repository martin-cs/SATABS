/*******************************************************************\

Module: Conversion to PROMELA

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#ifndef CPROVER_BOPPO_CONVERT_TO_PROGRAM_FORMULA_H
#define CPROVER_BOPPO_CONVERT_TO_PROGRAM_FORMULA_H

#include <context.h>
#include <std_code.h>

#include "program_formula.h"

void convert_to_program_formula(
  contextt &context,
  program_formulat &program_formula,
  formula_containert &formula_container,
  const std::string &error_label,
  bool inlining);

#endif
