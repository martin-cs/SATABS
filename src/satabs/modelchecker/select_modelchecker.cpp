/*******************************************************************\

Module: Modelchecker Selection

Authors: Daniel Kroening, kroening@kroening.com
Karen Yorav

Date: June 2003

\*******************************************************************/

#include <util/options.h>

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

modelcheckert *select_modelchecker(const optionst &options)
{
  const std::string name=options.get_option("modelchecker");

  modelcheckert *m=0;

  const unsigned max_threads=options.get_unsigned_int_option("max-threads");

  if(name=="boom")
    m=new modelchecker_boolean_programt(
        modelchecker_boolean_programt::BOOM, max_threads);
  else if(name=="boppo")
    m=new modelchecker_boolean_programt(
        modelchecker_boolean_programt::BOPPO, max_threads);
  else if(name=="cmu-smv")
    m=new modelchecker_smvt(modelchecker_smvt::CMU_SMV);
  else if(name=="cadence-smv")
    m=new modelchecker_smvt(modelchecker_smvt::CADENCE_SMV);
  else if(name=="nusmv")
    m=new modelchecker_smvt(modelchecker_smvt::NUSMV);
  else if(name=="satmc")
    m=new modelchecker_smvt(modelchecker_smvt::SATMC);
  else if(name=="spin")
    m=new modelchecker_spint();
  else
    throw "unknown modelchecker: "+name;

  assert(m!=0);

  if(options.get_bool_option("loop-detection"))
    m->enable_loop_detection();

  return m;
}
