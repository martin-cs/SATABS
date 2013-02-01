/*******************************************************************\

Module: Parsing Command Line Options for CEGAR

Author: Daniel Kroening
Karen Yorav

Date: June 2003

\*******************************************************************/

#include <iostream>
#include <memory>

#include <message.h>
#include <string2int.h>
#include <options.h>
#include <config.h>

#include <goto-symex/xml_goto_trace.h>

#include <cbmc/xml_interface.h>
#include <cbmc/version.h>

#include "cmdline_options.h"
#include "satabs_safety_checker.h"
#include "version.h"

#include "modelchecker/select_modelchecker.h"
#include "simulator/select_simulator.h"
#include "refiner/select_refiner.h"
#include "prepare/prepare.h"
#include "abstractor/select_abstractor.h"
#include "prepare/concrete_model.h"
#include "abstractor/abstractor.h"
#include "modelchecker/modelchecker.h"
#include "refiner/refiner.h"
#include "simulator/simulator.h"

/*******************************************************************\

Function: cmdline_optionst::get_command_line_options

Inputs:

Outputs:

Purpose: Parse and store options

\*******************************************************************/

void cmdline_optionst::get_command_line_options(optionst &options)
{
  options.set_option("bounds-check", cmdline.isset("bounds-check"));
  options.set_option("div-by-zero-check", cmdline.isset("div-by-zero-check"));
  options.set_option("pointer-check", cmdline.isset("pointer-check"));
  options.set_option("assertions", !cmdline.isset("no-assertions"));
  options.set_option("assumptions", !cmdline.isset("no-assumptions"));
  options.set_option("simplify", !cmdline.isset("no-simplify"));
  options.set_option("signed-overflow-check", cmdline.isset("signed-overflow-check"));
  options.set_option("unsigned-overflow-check", cmdline.isset("unsigned-overflow-check"));
  options.set_option("nan-check", cmdline.isset("nan-check"));

  if(cmdline.isset("error-label"))
    options.set_option("error-label", cmdline.getval("error-label"));

  if(cmdline.isset("iterations"))
    options.set_option("iterations", cmdline.getval("iterations"));
  else
    options.set_option("iterations", 100);

  options.set_option("concurrency", cmdline.isset("concurrency"));
  options.set_option("passive-nondet",
      cmdline.isset("passive-nondet"));

  // refiner
  if(cmdline.isset("refiner"))
    options.set_option("refiner", cmdline.getval("refiner"));
  else
    options.set_option("refiner", "wp");

  if(cmdline.isset("max-new-predicates"))
    options.set_option("max-new-predicates",
        cmdline.getval("max-new-predicates"));
  else
    options.set_option("max-new-predicates", -1);

  options.set_option("prefer-non-pointer-predicates",
      cmdline.isset("prefer-non-pointer-predicates"));

  options.set_option("remove-equivalent-predicates",
      cmdline.isset("remove-equivalent-predicates"));

  options.set_option("prefix-first", cmdline.isset("prefix-first"));

  options.set_option("no-mixed-predicates",
      cmdline.isset("no-mixed-predicates"));

  options.set_option("no-passive-constrain",
      cmdline.isset("no-passive-constrain") ||
      cmdline.isset("passive-nondet"));

  options.set_option("monotone-constrain", cmdline.isset("montone-constrain"));

  // -1 means use unsplit prover
  if(cmdline.isset("ipplimit"))
    options.set_option("ipplimit",
        cmdline.getval("ipplimit"));
  else
    options.set_option("ipplimit", -1);

  // abstractor
  if(cmdline.isset("abstractor"))
    options.set_option("abstractor", cmdline.getval("abstractor"));
  else
    options.set_option("abstractor", "wp");

  if(cmdline.isset("max-cube-length"))
    options.set_option("max-cube-length", cmdline.getval("max-cube-length"));
  else
    options.set_option("max-cube-length", 3);

  // model checker
  if(cmdline.isset("modelchecker"))
    options.set_option("modelchecker", cmdline.getval("modelchecker"));
  else
    options.set_option("modelchecker", "boom");

  // boom's default thread bound of 2 is too small
  if(cmdline.isset("max-threads"))
    options.set_option("max-threads", cmdline.getval("max-threads"));
  else
    options.set_option("max-threads", 5);

  options.set_option("build-tts", cmdline.isset("build-tts"));

  options.set_option("full-inlining", cmdline.isset("full-inlining"));

  options.set_option("loop-detection", cmdline.isset("loop-detection"));

  // simulator
  if(cmdline.isset("simulator"))
    options.set_option("simulator", cmdline.getval("simulator"));
  else
    options.set_option("simulator", "sat");

  options.set_option("no-path-slicing", cmdline.isset("no-path-slicing"));

  options.set_option("shortest-prefix", cmdline.isset("shortest-prefix"));
}

/*******************************************************************\

Function: cmdline_optionst::doit

Inputs:

Outputs:

Purpose: Parse and store options

\*******************************************************************/

int cmdline_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << SATABS_VERSION << std::endl;
    return 0;
  }

  optionst options;  
  get_command_line_options(options);

  // context that can be changed within the CEGAR loop
  contextt shadow_context;

  preparet prepare(cmdline, options, shadow_context);

  message_handlert &message_handler=prepare.ui_message_handler;

  // set the same verbosity for all
  int verbosity=6;
  if(cmdline.isset("v"))
    verbosity=safe_str2int(cmdline.getval("v"));

  prepare.set_verbosity(verbosity);

  // get configuration

  config.set(cmdline);

  // Parse input program, convert to goto program

  {
    int prepare_return_value=prepare.doit();
    if(prepare_return_value>=0)
      return prepare_return_value;
  }

  try
  {
    messaget message(message_handler);

    concrete_modelt concrete_model(prepare.ns, prepare.goto_functions);

    loop_componentt::argst args(
        message_handler, concrete_model);

    // The tools we need

    // finds predicates
    std::auto_ptr<refinert> refiner(
        select_refiner(options, args));

    // calculates abstract program
    std::auto_ptr<abstractort> abstractor(
        select_abstractor(options, args));

    // model checking engine
    std::auto_ptr<modelcheckert> modelchecker(
        select_modelchecker(options, args));

    // simulator
    std::auto_ptr<simulatort> simulator(
        select_simulator(options, args, prepare.shadow_context));

    // set their verbosity -- all the same for now
    refiner->set_verbosity(verbosity);
    abstractor->set_verbosity(verbosity);
    modelchecker->set_verbosity(verbosity);
    simulator->set_verbosity(verbosity);    

    satabs_safety_checker_baset satabs_safety_checker(
        prepare.ns,
        *abstractor,
        *refiner,
        *modelchecker,
        *simulator);

    satabs_safety_checker.initial_predicates=
      prepare.user_provided_predicates;

    satabs_safety_checker.set_message_handler(message_handler);
    satabs_safety_checker.ui=prepare.get_ui();    
    satabs_safety_checker.max_iterations=options.get_int_option("iterations");
    satabs_safety_checker.save_bps=cmdline.isset("save-bps");    
    satabs_safety_checker.build_tts=cmdline.isset("build-tts");    
    satabs_safety_checker.concurrency_aware=cmdline.isset("concurrency");
    satabs_safety_checker.write_csv_stats=cmdline.isset("csv-stats");
    satabs_safety_checker.set_verbosity(verbosity);

    switch(satabs_safety_checker(prepare.goto_functions))
    {
      case safety_checkert::SAFE:
        message.result("VERIFICATION SUCCESSFUL");

        if(prepare.get_ui()==ui_message_handlert::XML_UI)
        {
          xmlt xml("cprover-status");
          xml.data="SUCCESS";
          std::cout << xml << std::endl;
        }

        return 0;

      case safety_checkert::UNSAFE:
        if(prepare.get_ui()==ui_message_handlert::XML_UI)
        {
          xmlt xml1;
          convert(concrete_model.ns, satabs_safety_checker.error_trace, xml1);
          std::cout << xml1 << std::endl;

          xmlt xml2("cprover-status");
          xml2.data="FAILURE";
          std::cout << xml2 << std::endl;
        }
        else
        {
          message.result("Counterexample:");
          show_goto_trace(std::cout, concrete_model.ns,
              satabs_safety_checker.error_trace);
          message.result("VERIFICATION FAILED");
        }

        return 10;

      case safety_checkert::ERROR:
      default:;
              return 12;
    }
  }

  catch(const char *e)
  {
    prepare.error(e);
    return 1;
  }

  catch(const std::string e)
  {
    prepare.error(e);
    return 1;
  }

  catch(std::bad_alloc)
  {
    prepare.error("Out of memory");
    return 100;
  }

  return 0;
}

/*******************************************************************\

Function: cmdline_optionst::help

Inputs:

Outputs:

Purpose: display command line help

\*******************************************************************/

void cmdline_optionst::help()
{
  std::cout <<
    "\n"
    "* *          SATABS " SATABS_VERSION " - Copyright (C) 2003-2012           * *\n"
    "* *                     based on CBMC " CBMC_VERSION "                   * *\n"
    "* *              Daniel Kroening, Edmund Clarke             * *\n"
    "* *                  Oxford University, CMU                 * *\n"
    "* *                  kroening@kroening.com                  * *\n"
    "* *        Protected in part by U.S. patent 7,418,680       * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " satabs [-?] [-h] [--help]    show help\n"
    " satabs source.c              check given program\n"
    "\n"
    "Frontend options:\n"
    " -I path                      set include path (C/C++)\n"
    " -D macro                     define preprocessor macro (C/C++)\n"
    " --16, --32, --64             Set width of machine word\n"
    " --LP64, --ILP64, --LLP64,\n"
    "   --ILP32, --LP32            set width of int, long and pointers\n"
    " --little-endian              Allow little-endian word-byte conversions\n"
    " --big-endian                 Allow big-endian word-byte conversions\n"
    " --unsigned-char              make \"char\" unsigned by default\n"
    " --show-goto-functions        show goto program\n"
    " --show-adjusted-functions    show partially inlined goto program\n"
    " --show-final-program         show goto program after inlining and instrumentation\n"
    " --ppc-macos                  set MACOS/PPC architecture\n"
#ifdef _WIN32
    " --i386-macos                 set MACOS/I386 architecture\n"
    " --i386-linux                 set Linux/I386 architecture\n"
    " --i386-win32                 set Windows/I386 architecture (default)\n"
    " --winx64                     set Windows/X64 architecture\n"
#else
#ifdef __APPLE__
    " --i386-macos                 set MACOS/I386 architecture (default)\n"
    " --i386-linux                 set Linux/I386 architecture\n"
    " --i386-win32                 set Windows/I386 architecture\n"
    " --winx64                     set Windows/X64 architecture\n"
#else
    " --i386-macos                 set MACOS/I386 architecture\n"
    " --i386-linux                 set Linux/I386 architecture (default)\n"
    " --i386-win32                 set Windows/I386 architecture\n"
    " --winx64                     set Windows/X64 architecture\n"
#endif
#endif
    " --no-arch                    don't set up an architecture\n"
    " --round-to-nearest           IEEE floating point rounding mode (default)\n"
    " --round-to-plus-inf          IEEE floating point rounding mode\n"
    " --round-to-minus-inf         IEEE floating point rounding mode\n"
    " --round-to-zero              IEEE floating point rounding mode\n"
    "\n"
    "Program instrumentation options:\n"
    " --bounds-check               enable array bounds checks\n"
    " --div-by-zero-check          enable division by zero checks\n"
    " --pointer-check              enable pointer checks\n"
    " --signed-overflow-check      enable arithmetic over- and underflow checks\n"
    " --unsigned-overflow-check    enable arithmetic over- and underflow checks\n"
    " --nan-check                  check floating-point for NaN\n"
    " --show-claims                only show claims\n"
    " --show-loops                 show the loops in the program\n"
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --error-label label          check that label is unreachable\n"
    " --string-abstraction         enable additional char* property tracking\n"
    " --no-slicing                 disable reachability slicing\n"
    "\n"
    "Modelchecker options:\n"
    " --function name              set main function name\n"
    " --full-inlining              perform full function inlining\n"
    " --show-value-sets            just show the value set propagation\n"
#if 0
    " --show-invariant-sets        just show the invariant set propagation\n"
    " --no-invariant-sets          UNDOCUMENTED\n"
#endif
    " --claim #                    check a specific claim only\n"
    " --loop-detection             use heuristic to detect loops\n"
    " --modelchecker name          set the modelchecker to be used\n"
    " --abstractor name            set the abstractor to be used\n"
    " --refiner name               set the refiner to be used\n"
    " --simulator name             set the simulator to be used\n"
    " --max-new-predicates #       set bound on number of new predicates added\n"
    "                                 on each iteration\n"
    " --prefer-non-pointer-predicates\n"
    "                              when adding up to 'max-new-predicates'\n"
    "                              predicates give preference to predicates that\n"
    "                              are not pointer equality tests\n"
    " --prefix-first               try predicate discovery in simulation before\n"
    "                                 falling back to transition refinement\n"
    " --remove-equivalent-predicates\n"
    "                              when adding predicates, make sure no two\n"
    "                              equivalent predicates are added\n"
    " --shortest-prefix            compute the shortest spurious prefix\n"
    " --max-cube-length #          for Cartesian abstraction, set maximum length\n"
    "                              of cube to be considered (default: 3)\n"
    " --iterations #               set maximum number of refinement iterations (default: 100)\n"
    " --predicates file            read predicates from file\n"
    " --no-path-slicing            disable path slicer\n"
    " --save-bps                   save a Boolean program for each iteration\n"
    " --csv-stats                  write statistics for each iteration to cegar.csv\n"
    " --build-tts                  if modelchecking using boom or boppo, also write\n"
    "                                 thread transition systems to .tts files\n"
    "                                 requires --full-inlining\n"
    " --concurrency                use CAV'11 method to handle concurrency\n"
    " --max-threads #              when \"concurrency\" is on, specifies maximum\n"
    "                                 number of threads to spawn (default: 2)\n"
    " --no-passive-constrain       when \"concurrency\" is on, do not constrain broadcasts\n"
    " --passive-nondet             when \"concurrency\" is on, always force passive\n"
    "                                 predicates to nondet on broadcast; implies --no-passive-constrain\n"
    " --no-mixed-predicates        don't add predicates involving shared and local variables\n"
    " --monotone-constrain         when \"concurrency\" is on, ensure monotonicity in transition refinement\n"
#ifdef HAVE_IPP
    " --ipplimit                   limit for interpolating prover\n"
#endif
    "\n"
    "Other options:\n"
    " --v #                        verbosity level\n"
    " --version                    show version and exit\n"
    "\n";
}
