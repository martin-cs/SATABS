/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#ifndef CPROVER_BOPPO_PARSEOPTIONS_H
#define CPROVER_BOPPO_PARSEOPTIONS_H

#include <parseoptions.h>
#include <langapi/language_ui.h>

class boppo_parseoptionst:public parseoptions_baset,
                                 language_uit
{
 public:
  virtual int doit();
  virtual void help();

  boppo_parseoptionst(int argc, const char **argv);
};

#endif
