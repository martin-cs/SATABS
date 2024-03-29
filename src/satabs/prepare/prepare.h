/*******************************************************************\

Module: "Preprocess" C program for CEGAR

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

Purpose: Preprocess the C program and convert it into a GOTO
         program.

\*******************************************************************/

#ifndef CPROVER_SATABS_PREPARE_H
#define CPROVER_SATABS_PREPARE_H

#include <langapi/language_ui.h>

#include <goto-programs/goto_functions.h>

class cmdlinet;
class optionst;

class preparet:public language_uit
{
public:
  preparet(
    const cmdlinet &_cmdline,
    const optionst &options);

  int doit();

  goto_functionst goto_functions;
  std::vector<exprt> user_provided_predicates;

private:
  const cmdlinet &cmdline;
  const optionst &options;

  void get_initial_state();
  int get_goto_program();

  void replace_dynamic_allocation(goto_programt &goto_program);
  void replace_dynamic_allocation(goto_functionst &goto_functions);

  void register_languages();
};

#endif
