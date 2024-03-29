/*******************************************************************\

 Module: Command Line Parsing

 Author: CM Wintersteiger

\*******************************************************************/

#include <iostream>

#include <util/string2int.h>
#include <util/config.h>
#include <util/time_stopping.h>
#include <util/xml.h>

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/string_instrumentation.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_properties.h>

#include <analyses/invariant_propagation.h>
#include <analyses/natural_loops.h>

#include <satabs/prepare/prepare_functions.h>
#include <termination/instrumentation.h>
#include <termination/termination.h>
#include <termination/termination_slicer.h>
#include <termination/transform_loops.h>

#include "tan_parse_options.h"
#include "version.h"
#include "languages.h"

/*******************************************************************

 Function: tan_parse_optionst::tant

 Inputs:

 Outputs:

 Purpose: constructor

 \*******************************************************************/

tan_parse_optionst::tan_parse_optionst(int argc, const char **argv):
  parse_options_baset(TAN_OPTIONS, argc, argv),
  language_uit("TAN" TAN_VERSION, cmdline)
{
}

/*******************************************************************

 Function: tan_parse_optionst::doit

 Inputs:

 Outputs:

 Purpose: invoke main modules

 \*******************************************************************/

int tan_parse_optionst::doit()
{
  register_languages();

  if(check_and_set_options()) return TAN_UNKNOWN;
  if(from_file(cmdline.args[0])) return TAN_UNKNOWN;  
  if(prepare()) return TAN_UNKNOWN;
  
  return analyze();  
}

/*******************************************************************\
  
 Function: tan_parse_optionst::help

 Inputs:

 Outputs:

 Purpose: display command line help

 \*******************************************************************/

void tan_parse_optionst::help()
{    
  std::cout <<"\n"
    "* * *                 TAN " TAN_VERSION
  " - Copyright (C) 2009               * * *\n"
  "              Daniel Kroening & Christoph M. Wintersteiger\n"
  "\n"
  "Usage:                         Purpose:\n"
  "\n"
  " tan [-?] [-h] [--help]        show help\n"
  " tan [options] <file>          run on goto-binary `file'\n"
  "\n"
  "Display options:\n"
  "--version                      show version information\n"
  "--verbosity <int>              set verbosity (default: 6)\n"
  "--show-model                   show the model as loaded\n"
  "--show-prepared-model          show the model after preparation\n"
  "--string-abstraction           enable string abstraction\n"
  "--no-invariant-propagation     disable invariant propagation\n"
  "--no-value-sets                disable value sets (pointer analysis)\n"
  "--function                     set entry point\n"
  "--property #                   check only property #\n"
  "--show-properties              show all generated properties\n"
  "\n"
  "Termination Engine Options:\n"
  "--engine <engine>              Select one of the termination engines:\n"
  "          cta                  Compositional Termination Analysis (default)\n"
#ifdef HAVE_INTERPOLATION
  "          ita                  Interpolating Termination Analysis\n"
#endif
  "          enum                 Path Enumeration\n"
  "          bre                  Binary Reachability Engine\n"    
  "          direct               direct approach (Biere et al.)\n"  
  "--ranksynthesis <m>            choose rank synthesis method <m>:\n"
  "          sat                  SAT enumeration (default)\n"
  "          qbf                  QBF w/ unconstrained coefficients\n"
  "          qbfC                 QBF w/ constrained coefficients\n"
  "          rf                   Linear rank functions via Rankfinder\n"
  "          seneschal            Linear rank functions via Seneschal\n"
  "          qbfbA                QBF Bitwise affine functions\n"
  "          qbfbC                QBF Bitwise conjunctive functions\n"
  "          qbfbD                QBF Bitwise disjunctive functions\n"
  "          qbfbN                QBF Bitwise bottom (no functions)\n"
  "          qbfbP                QBF Bitwise projective functions\n"
  "          none                 No ranking functions\n"
  "--unranked-method <m>          how to react to unranked paths\n"
  "          none                 report the loop as non-terminating (default)\n"
  "          precondition         check reachability of wp(path) (using CEGAR)\n"
  "          bmc-precondition     check reachability of wp(path) (using BMC)\n"
  "          cegar                check loop reachability (using CEGAR)\n"
  "          bmc                  check loop reachability (using BMC)\n"
  "--no-loop-slicing              disable loop slicing (BRE and direct only)\n"  
  "\n";
}

/*******************************************************************\
  
 Function: tan_parse_optionst::check_and_set_options

 Inputs:

 Outputs:

 Purpose: 

 \*******************************************************************/

bool tan_parse_optionst::check_and_set_options()
{
  if(config.set(cmdline))
  {
    usage_error();
    return true;
  }

  if(cmdline.isset("version"))
  {
    std::cout << TAN_VERSION << std::endl;
    return true;
  }
    
  {
    int verbosity=6;
    if(cmdline.isset("verbosity"))
      verbosity=unsafe_string2int(cmdline.get_value("verbosity"));
    ui_message_handler.set_verbosity(verbosity);
  }
  
  if(cmdline.args.size()==0)
  {
    error() << "Please provide a goto-binary as input file" << eom;
    return 1;
  }
  else if(cmdline.args.size()>1)
  {
    error() << "Multiple input files not supported" << eom;
    return 1;
  }
  
  std::string engine="cta";
  if(cmdline.isset("engine"))
    engine=cmdline.get_value("engine");
  
  if(cmdline.isset("no-loop-slicing") &&
     engine!="direct" && engine!="bre")
    warning() << "Warning: --no-loop-slicing is only available "
                 "with the following engines: bre, direct." << eom;
  
  if(cmdline.isset("unranked-method"))
  {
    std::string u_mode=cmdline.get_value("unranked-method");
    if(u_mode!="none" && u_mode!="precondition" && u_mode!="bmc-precondition" &&
        u_mode!="cegar" && u_mode!="bmc")
      warning() << "Warning: unknown unranked-method." << eom;
  }  
  
  return false;
}

/*******************************************************************\
  
 Function: tan_parse_optionst::from_file

 Inputs:

 Outputs:

 Purpose: 

 \*******************************************************************/

bool tan_parse_optionst::from_file(const std::string &filename)
{  
  std::ifstream infile(filename.c_str());

  if(!infile)
  {
    error() << "Error opening file `" << filename << "'" << eom;
    return true;
  }  

  status() << "Loading `" << filename << "'" << eom;

  if(read_goto_binary(filename, symbol_table, goto_functions, get_message_handler()))
  {
    error() << "Error reading file `" << filename << "'" << eom;
    return true;
  }
  
  if(cmdline.isset("show-program"))
  {
    goto_functions.output(namespacet(symbol_table), std::cout);
    return true;    
  }
  
  return false;
}

/*******************************************************************\
  
 Function: tan_parse_optionst::prepare

 Inputs:

 Outputs:

 Purpose: 

 \*******************************************************************/

bool tan_parse_optionst::prepare()
{
  message_handlert &mh=get_message_handler();
  
  const namespacet ns(symbol_table);
  
  if(cmdline.isset("show-model"))
  {
    goto_functions.output(ns, std::cout);
    return true;
  }
  
  if(cmdline.isset("string-abstraction"))
    string_instrumentation(symbol_table, mh, goto_functions);
  
  status() << "Removing function pointers" << eom;
  remove_function_pointers(symbol_table, goto_functions, false);

  status() << "Removing unused functions" << eom;
  remove_unused_functions(goto_functions, mh);

  status() << "Transforming loops" << eom;
  transform_loops(goto_functions, symbol_table, mh);
  
  status() << "Partial inlining" << eom;
  goto_partial_inline(goto_functions, ns, mh);
  
  // we do this again, to remove all the functions that are inlined now
  remove_unused_functions(goto_functions, mh);

  status() << "Adjusting functions" << eom;
  prepare_functions(symbol_table, goto_functions, mh);
  
  if(cmdline.isset("string-abstraction"))
  {
    status() << "String Abstraction" << eom;
    string_abstraction(symbol_table, mh, goto_functions);
  }
    
  goto_functions.compute_location_numbers();

  #if 0
  status() << "Natural loops:" << eom;

  forall_goto_functions(it, goto_functions)
  {
    natural_loopst nl;
    nl(it->second.body);		
    nl.output(std::cout);
  }
  #endif
		
  status() << "Termination instrumentation" << eom;
  termination_instrumentert::modet instrumenter_mode=
    termination_instrumentert::T_RANKSYNTH;
    
  if(cmdline.isset("engine") &&
     cmdline.get_value("engine")=="direct")
  {
    if(cmdline.isset("ranksynthesis"))
        warning() << "Warning: --ranksynthesis does not make sense with --direct." << eom;

    instrumenter_mode = termination_instrumentert::T_DIRECT;
  }

  termination_instrumentert termination(goto_functions, symbol_table, mh, instrumenter_mode);
  unsigned loopcount=termination.instrument();

  goto_functions.update();
  label_properties(goto_functions);
    
  if(cmdline.isset("show-properties"))
  {
    if(loopcount==0)
      status() << "No properties" << eom;
    else
      show_properties(ns, get_ui(), goto_functions);
    
    return true;
  }
  
  if(!cmdline.isset("no-invariant-propagation"))
  {
    absolute_timet before=current_time();
    
    // This is done without value_set_analysis being initialized
    value_set_analysist vsa(ns);
    invariant_propagationt ip(ns, vsa);
        
    status() << "Invariant Propagation" << eom;
    
    try 
    {
      ip(goto_functions);    
  
      if(cmdline.isset("show-invariant-sets"))
      {
        ip.output(goto_functions, std::cout);
        return true;
      }
    
      ip.simplify(goto_functions);
      ip.clear();
    }

    catch (const std::bad_alloc &e) 
    {
      ip.clear();
      
      warning() << "Warning: Invariant propagation canceled because it "
                   "exceeded the memory limit" << eom;
    }
    
    status() << "Invariant Propagation: "
             << (current_time()-before) << " s total" << eom;
  }

  // set property
  if(cmdline.isset("property"))
    set_properties(goto_functions, cmdline.get_values("property"));
  
  if(cmdline.isset("show-prepared-model"))
  {
    goto_functions.output(ns, std::cout);
    return true;
  }
  
  return false;
}

/*******************************************************************\
  
 Function: tan_parse_optionst::analyze

 Inputs:

 Outputs:

 Purpose: 

 \*******************************************************************/

tan_resultt tan_parse_optionst::analyze()
{  
  const namespacet ns(symbol_table);
  value_set_analysist value_set_analysis(ns);
  invariant_propagationt invariant_propagation(ns, value_set_analysis);
  
  std::vector<exprt> up_predicates;
  unsigned int max_iterations=0;
  
  termination_prover_modet engine=TP_COMPOSITIONAL;
  
  if(cmdline.isset("engine"))
  {
    std::string estr=cmdline.get_value("engine");
    
    if(estr=="bre") engine=TP_BINARY_REACHABILITY;
    else if(estr=="direct") engine=TP_DIRECT;
    else if(estr=="enum") engine=TP_PATH_ENUMERATION;
    else if(estr=="cta") engine=TP_COMPOSITIONAL;
#ifdef HAVE_INTERPOLATION
    else if(estr=="ita") engine=TP_INTERPOLATING;
#endif
    else
      throw ("Unknown termination engine selected");
  }
  
  termination_resultt
    res=termination(engine,
                    cmdline, goto_functions, symbol_table, 
                    value_set_analysis, invariant_propagation, *message_handler,
                    get_ui(),
                    up_predicates, max_iterations);

  if(get_ui()==ui_message_handlert::XML_UI)
  {
    if(res==T_TERMINATING || res==T_NONTERMINATING)
    {
      xmlt xml("cprover-status");
      xml.data=(res==T_NONTERMINATING?"FAILURE":"SUCCESS");
      std::cout << xml;
      std::cout << std::endl;
    }
  }
  
  switch(res)
  {
  case T_TERMINATING: return TAN_TERMINATING;
  case T_NONTERMINATING: return TAN_NONTERMINATING;
  default: return TAN_ERROR;
  }  
}
