/*******************************************************************\

Module: Modelchecker Selection

Authors: Daniel Kroening, kroening@kroening.com
Karen Yorav

Date: June 2003

\*******************************************************************/

#include <options.h>

#include "select_modelchecker.h"
#include "modelchecker_boolean_program.h"
#include "modelchecker_smv.h"
#include "modelchecker_spin.h"

/*******************************************************************\

Function: select_modelchecker

Inputs:

Outputs:

Purpose:

\*******************************************************************/

modelcheckert *select_modelchecker(
  const optionst &options,
  const loop_componentt::argst &args)
{
  const std::string name=options.get_option("modelchecker");

  modelcheckert *m=0;

  const bool concurrency=options.get_bool_option("concurrency");
  const unsigned max_threads=options.get_int_option("max-threads");
  const bool build_tts=options.get_bool_option("build-tts");

  assert(!build_tts ||
      (name=="boppo" && options.get_bool_option("full-inlining"))
      || name=="boom");

  if(name=="boom")
    m=new modelchecker_boolean_programt(args,
        modelchecker_boolean_programt::BOOM, max_threads,
        concurrency, build_tts);
  else if(name=="boppo")
    m=new modelchecker_boolean_programt(args,
        modelchecker_boolean_programt::BOPPO, max_threads,
        concurrency, build_tts);
  else if(name=="cmu-smv")
    m=new modelchecker_smvt(args, modelchecker_smvt::CMU_SMV, concurrency);
  else if(name=="cadence-smv")
    m=new modelchecker_smvt(args, modelchecker_smvt::CADENCE_SMV, concurrency);
  else if(name=="nusmv")
    m=new modelchecker_smvt(args, modelchecker_smvt::NUSMV, concurrency);
  else if(name=="satmc")
    m=new modelchecker_smvt(args, modelchecker_smvt::SATMC, concurrency);
  else if(name=="spin")
    m=new modelchecker_spint(args, concurrency);
  else
    throw "unknown modelchecker: "+name;

  assert(m!=0);

  if(options.get_bool_option("loop-detection"))
    m->enable_loop_detection();

  return m;
}
