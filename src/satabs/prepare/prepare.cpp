/*******************************************************************\

Module: Prepare a C program for use by CEGAR

Author: Daniel Kroening
Karen Yorav

Date: June 2003

\*******************************************************************/

#include <iostream>

#include <expr_util.h>
#include <get_module.h>
#include <i2string.h>
#include <xml.h>
#include <xml_irep.h>
#include <symbol_table.h>
#include <cmdline.h>

#include <ansi-c/ansi_c_language.h>

#include <goto-programs/show_claims.h>
#include <goto-programs/set_claims.h>
#include <goto-programs/reachability_slicer.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/string_instrumentation.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/link_to_library.h>

#include <analyses/goto_check.h>

#include <langapi/language_util.h>
#include <langapi/mode.h>
#include <langapi/languages.h>

#include <pointer-analysis/goto_program_dereference.h>
#include <pointer-analysis/add_failed_symbols.h>

#include "../version.h"
#include "prepare.h"
#include "prepare_functions.h"
#include "get_predicates.h"

#include "satabs_inline.h"

#define MAX_BLOCK_SIZE 1

/*******************************************************************\

Function: preparet::preparet

Inputs:

Outputs:

Purpose: convert input program into goto program

\*******************************************************************/

preparet::preparet(
    const cmdlinet &_cmdline,
    const optionst &_options): 
  language_uit("SATABS " SATABS_VERSION, _cmdline),
  cmdline(_cmdline),
  options(_options)
{
}

/*******************************************************************\

Function: preparet::doit

Inputs:

Outputs:

Purpose: convert input program into goto program

\*******************************************************************/

int preparet::doit()
{
  register_languages();

  try
  {
    // do we have a goto binary?
    if(cmdline.args.size()==1 &&
       is_goto_binary(cmdline.args[0]))
    {
      status("Reading GOTO program from file");

      if(read_goto_binary(cmdline.args[0],
            symbol_table, goto_functions,
            get_message_handler()))
        return 1;

      config.ansi_c.set_from_symbol_table(symbol_table);
    }
    else
    {
      // from source
      
      // parsing
      if(parse()) return 1;

      // type checking
      if(typecheck()) return 1;

      // final adjustments
      if(final()) return 1;

      // see if we have a "main"

      if(symbol_table.symbols.find("main")==symbol_table.symbols.end())
      {
        error("failed to find entry point -- please provide a model");
        return 1;
      }

      status("Generating GOTO Program");

      goto_convert(
          symbol_table,
          goto_functions,
          get_message_handler());

      // we no longer need any parse trees or language files
      clear_parse();
    }

    {
      int return_value_get_sync_modules=get_sync_modules();
      if(return_value_get_sync_modules>=0)
        return return_value_get_sync_modules;
    }

    {
      int return_value_get_async_modules=get_async_modules();
      if(return_value_get_async_modules>=0)
        return return_value_get_async_modules;
    }

    if(cmdline.isset("show-claims"))
    {
      namespacet ns(symbol_table);
      show_claims(ns, get_ui(), goto_functions);
      return 0;
    }

    // get the user provided predicates

    if(cmdline.isset("predicates"))
    {
      namespacet ns(symbol_table);
      get_predicates(
          cmdline.getval("predicates"),
          get_message_handler(),
          ns,
          user_provided_predicates);
    }
  }

  catch(const char *e)
  {
    error(e);
    return 1;
  }

  catch(const std::string e)
  {
    error(e);
    return 1;
  }

  catch(int)
  {
    return 1;
  }

  return -1; // proceed!
}

/*******************************************************************\

Function: preparet::get_sync_modules

Inputs:

Outputs:

Purpose:

\*******************************************************************/

int preparet::get_sync_modules()
{
  return -1; // proceed!
}

/*******************************************************************\

Function: preparet::get_async_modules

Inputs:

Outputs:

Purpose:

\*******************************************************************/

int preparet::get_async_modules()
{
  namespacet ns(symbol_table);

  // finally add the library
  status("Adding CPROVER library");      
  link_to_library(
      symbol_table, goto_functions, get_message_handler());

  if(cmdline.isset("show-goto-functions"))
  {
    goto_functions.update();
    goto_functions.output(ns, std::cout);
    return 0;
  }

  unsigned functions=goto_functions.function_map.size();
  unsigned instructions=0;
  forall_goto_functions(it, goto_functions)
    instructions+=it->second.body.instructions.size();

  status(i2string(functions)+" functions, "+
      i2string(instructions)+" instructions.");

  if(cmdline.isset("string-abstraction"))
    string_instrumentation(
        symbol_table, get_message_handler(), goto_functions);

  {
    status("Removing function pointers");
    remove_function_pointers(
        symbol_table, goto_functions, cmdline.isset("pointer-check"));
  }

  status("Removing unused functions");
  remove_unused_functions(
      goto_functions, get_message_handler());

  // Boom requies full inlining.
  bool boom=
    !cmdline.isset("modelchecker") ||
    std::string(cmdline.getval("modelchecker"))=="boom";

  if(cmdline.isset("full-inlining") || boom)
  {
    status("Full inlining");

    satabs_inline(
      goto_functions,
      ns,
      get_message_handler());
  }
  else
  {
    // partially inline functions
    status("Partial inlining");

    satabs_partial_inline(
        goto_functions,
        ns,
        get_message_handler());

    // we do this again, to remove all the functions that are inlined now
    remove_unused_functions(
        goto_functions, get_message_handler());

    status("Adjusting functions");
    prepare_functions(
        symbol_table,
        goto_functions,
        get_message_handler());

    // show it?
    if(cmdline.isset("show-adjusted-functions"))
    {
      goto_functions.output(ns, std::cout);
      return 0;
    }
  }

  // add loop ids
  goto_functions.compute_loop_numbers();

  add_failed_symbols(symbol_table);

  // add generic checks
  goto_check(ns, options, goto_functions);

  if(cmdline.isset("string-abstraction"))
  {
    status("String Abstraction");
    string_abstraction(
        symbol_table,
        get_message_handler(),
        goto_functions);
  }  

  goto_functions.compute_location_numbers();

  // label claims
  label_claims(goto_functions);

  // set claim
  if(cmdline.isset("claim"))
    set_claims(
        goto_functions,
        cmdline.get_values("claim"));

  // reachability slice?
  if(!cmdline.isset("no-slicing"))
    reachability_slicer(goto_functions);

  // show it?

  if(cmdline.isset("show-final-program"))
  {
    goto_functions.output(ns, std::cout);
    return 0;
  }

  return -1; // proceed!
}

