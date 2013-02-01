/*******************************************************************\

Module: Command Line Parsing

Author: CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_TAN_PARSEOPTIONS_H
#define CPROVER_TAN_PARSEOPTIONS_H

#include <fstream>

#include <ui_message.h>
#include <parseoptions.h>
#include <context.h>

#include <langapi/language_ui.h>
#include <goto-programs/goto_functions.h>
#include <pointer-analysis/value_set_analysis.h>

#define TAN_OPTIONS \
  "(v):(version)(xml-ui)" \
  "(show-model)(show-prepared-model)" \
  "(function)(claim):(show-claims)" \
  "(string-abstraction)(no-invariant-propagation)(no-value-sets)" \
  "(no-loop-slicing)" \
  "(ranksynthesis):" \
  "(unranked-method):" \
  "(engine):"

typedef enum { TAN_UNKNOWN=0, 
               TAN_TERMINATING=10,
               TAN_NONTERMINATING=20, 
               TAN_ERROR=30 } tan_resultt;

class tan_parseoptionst:
  public parseoptions_baset,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  tan_parseoptionst(int argc, const char **argv);
  
private:
  contextt context;
  namespacet ns;
  goto_functionst goto_functions;

  // some stats
  unsigned loops_nonterminating;
  
  bool check_and_set_options();
  bool from_file(const std::string &filename);
  bool prepare();
  tan_resultt analyze();
  
  bool get_entry_point(
    goto_functionst::function_mapt::const_iterator &func_it,
    goto_programt::const_targett &entry);
  
  goto_programt::const_targett find_next_loop(
    goto_programt::const_targett current,
    const goto_programt &program,
    std::list<goto_programt::const_targett> &recursion_stack) const;
};

#endif
