/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#ifndef CPROVER_BOPPO_PARSEOPTIONS_H
#define CPROVER_BOPPO_PARSEOPTIONS_H

#include <util/parse_options.h>
#include <langapi/language_ui.h>

class boppo_parse_optionst:public parse_options_baset,
                                  language_uit
{
 public:
  virtual int doit();
  virtual void help();

  boppo_parse_optionst(int argc, const char **argv);
};

#endif
