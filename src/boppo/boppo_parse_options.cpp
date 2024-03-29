/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/*

  BOPPO
  Boolean Programs with Partial Order Reduction
  Copyright (C) 2003-2006 Daniel Kroening <kroening@kroening.com>

  Purpose: Main Module, Command Line Parsing

*/

#include <cassert>
#include <fstream>

#include <util/i2string.h>
#include <util/parse_options.h>
#include <util/cout_message.h>
#include <util/ui_message.h>
#include <util/namespace.h>
#include <util/time_stopping.h>
#include <util/config.h>
#include <util/threeval.h>

#include <langapi/mode.h>

#include <bplang/expr2bp.h>
#include <bplang/bp_language.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_convert.h>

#include <analyses/goto_check.h>

#include "convert_to_promela.h"
#include "convert_to_program_formula.h"
#include "boppo_parse_options.h"
#include "simulator.h"
#include "simulator_ct.h"
#include "version.h"

/*******************************************************************\

Function: boppo_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

boppo_parse_optionst::boppo_parse_optionst(int argc, const char **argv):
  parse_options_baset(
    "(promela)(smv)(show-boolean-program)(gui)"
    "(show-parse)(show-goto-program)(version)"
    "(show-program-formula)l:(por)(ct)"
    "(small-history)(statistics)(tvs)"
    "(show-program-variables)(compact-trace)"
    "(show-goto-functions)(loop-detection)(slam-race)"
    "(no-qbf-cache)(show-alive)(show-cycles)"
    "otcmuf",
    argc, argv),
  language_uit("BOPPO " BOPPO_VERSION, cmdline)
{
}

/*******************************************************************\

Function: boppo_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int boppo_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << BOPPO_VERSION << std::endl;
    return 0;
  }

  if(cmdline.args.size()==0)
  {
    usage_error();
    return 1;
  }

  // be compatible with Bebop
  bool slam=cmdline.isset('f');
  
  bool enable_partial_order_reduction=cmdline.isset("por");
  bool enable_small_history=cmdline.isset("small-history");
  bool enable_qbf_cache=!cmdline.isset("no-qbf-cache");
  bool enable_tvs=cmdline.isset("tvs");
  bool enable_ct=cmdline.isset("ct");

  //
  // parsing
  //
  
  register_language(new_bp_language);

  if(parse()) return 1;

  if(cmdline.isset("show-parse"))
  {
    language_files.show_parse(std::cout);
    return 0;
  }

  //
  // type checking
  //

  if(typecheck()) return 3;

  // final adjustments

  if(final()) return 5;

  // we no longer need any parse trees or language files
  clear_parse();

  try
  {
    std::string error_label;

    if(cmdline.isset('l'))
      error_label=cmdline.get_value('l');

    // do actual job
    if(cmdline.isset("promela"))
      convert_to_promela(symbol_table, std::cout);
    else if(cmdline.isset("show-goto-functions"))
    {
      goto_functionst goto_functions;
      
      goto_convert(
        symbol_table,
        goto_functions,
        ui_message_handler);

      // we do want the assertions
      optionst options;
      options.set_option("assertions", true);  
      options.set_option("error-label", error_label);
      
      namespacet ns(symbol_table);    
      goto_check(ns, options, goto_functions);
      goto_functions.output(ns, std::cout);
    }
    else if(cmdline.isset("show-program-formula") ||
            cmdline.isset("show-program-variables") ||
            cmdline.isset("show-alive") ||
            cmdline.isset("show-cycles") ||
            cmdline.isset("statistics"))
    {
      formula_containert formula_container;
      program_formulat program_formula;

      convert_to_program_formula(
        symbol_table, 
        program_formula,
        formula_container,
        error_label,
        false); // inlining

      if(cmdline.isset("statistics"))
        program_formula.show_statistics(std::cout);
      else if(cmdline.isset("show-program-variables"))
        std::cout << program_formula.variables;
      else if(cmdline.isset("show-alive"))
        program_formula.show_alive(std::cout);
      else if(cmdline.isset("show-cycles"))
      {
        namespacet ns(symbol_table);    
        program_formula.show_cycles(ns, std::cout);
      }
      else
      {
        for(program_formulat::function_mapt::const_iterator
            it=program_formula.function_map.begin();
            it!=program_formula.function_map.end();
            it++)
        {
          std::cout << it->first << std::endl;
          std::cout << "-----------------------------------------------------------\n";
          std::cout << std::endl;
          std::cout << it->second.body;
          std::cout << std::endl;
        }
      }
    }
    else if(enable_ct)
    {
      std::cout << "Building Program Formula" << std::endl;
      
      formula_containert formula_container;
      program_formulat program_formula;
      
      convert_to_program_formula(
        symbol_table, 
        program_formula,
        formula_container,
        error_label,
        false); // inlining 

      std::cout << "Mode: CT" << std::endl;

      simulator_ctt simulator(program_formula);
      simulator.compact_trace=cmdline.isset("compact-trace");
      simulator.slam=slam;
      simulator.slam_race=cmdline.isset("slam-race");

      assert(cmdline.args.size()>=1);
      
      simulator.simulator();
      
      if(slam)
      {
        if(simulator.error_state_found)
          return 0;
        else
          return 2;
      }

      return 0;
    }
    else
    {
      std::cout << "Building Program Formula" << std::endl;
      
      formula_containert formula_container;
      program_formulat program_formula;
      
      convert_to_program_formula(
        symbol_table, 
        program_formula,
        formula_container,
        error_label,
        true); // inlining 

      std::cout << "Partial Order Reduction: "
                << (enable_partial_order_reduction?
                   "YES":"NO") << std::endl;
      
      std::cout << "Small history: "
                << (enable_small_history?
                   "YES":"NO") << std::endl;

      std::cout << "QBF Cache: "
                << (enable_qbf_cache?
                   "YES":"NO") << std::endl;

      std::cout << "Mode: "
                << (enable_tvs?
                    "TVS":"FULL") << std::endl;

      simulatort simulator(program_formula);

      simulator.enable_partial_order_reduction=
        enable_partial_order_reduction;
      simulator.enable_qbf_cache=
        enable_qbf_cache;
      simulator.enable_small_history=
        enable_small_history;
        
      simulator.mode=enable_tvs?simulatort::TVS:
                     simulatort::FULL;
      
      simulator.slam=slam;
      simulator.compact_trace=cmdline.isset("compact-trace");
      simulator.slam_race=cmdline.isset("slam-race");
      simulator.loops=cmdline.isset("loop-detection");

      assert(cmdline.args.size()>=1);
      simulator.slam_file=cmdline.args[0];
      
      simulator.simulator();
      
      if(slam)
      {
        if(simulator.error_state_found)
          return 0;
        else
          return 2;
      }
      
      return 0;
    }
  }

  catch(const char *error)
  {
    std::cerr << "BOPPO ERROR: " << error << std::endl;
    return 3;
  }
  
  catch(const std::string &error)
  {
    std::cerr << "BOPPO ERROR: " << error << std::endl;
    return 3;
  }

  catch(int)
  {
    std::cerr << "BOPPO ERROR" << std::endl;
    return 3;
  }
  
  return 0;
}

/*******************************************************************\

Function: boppo_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void boppo_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *     BOPPO - Copyright (C) 2003-2004 Daniel Kroening     * *\n"
    "* *         ETH Zuerich, Computer Science Department        * *\n"
    "* *                  kroening@kroening.com                  * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " boppo [-?] [-h] [--help]     show help\n"
    " boppo file ...               source file names\n"
    "\n"
    "Additonal options:\n"
    " -l label                     check for reachability of label\n"
    " --por                        enable partial order reduction\n"
    " --compact-trace              show error trace with one line per transition\n"
    " --loop-detection             enable loop detection\n"
    "\n";
}
