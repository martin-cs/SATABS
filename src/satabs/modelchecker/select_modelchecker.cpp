/*******************************************************************\

Module: Modelchecker Selection

Authors: Daniel Kroening, kroening@kroening.com
         Karen Yorav

Date: June 2003

\*******************************************************************/

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
  const cmdlinet &cmdline,
  const loop_componentt::argst &args)
{
  std::string name=
    cmdline.isset("modelchecker")?cmdline.getval("modelchecker"):"cadence-smv";

  unsigned max_threads=0;
  if(cmdline.isset("max-threads"))
    max_threads=atoi(cmdline.getval("max-threads"));
    
  modelcheckert *m(NULL);

  if(name=="boppo")
    m=new modelchecker_boolean_programt(args, modelchecker_boolean_programt::BOPPO, max_threads, cmdline.isset("concurrency"));
  else if(name=="cmu-smv")
    m=new modelchecker_smvt(args, modelchecker_smvt::CMU_SMV, cmdline.isset("concurrency"));
  else if(name=="cadence-smv")
    m=new modelchecker_smvt(args, modelchecker_smvt::CADENCE_SMV, cmdline.isset("concurrency"));
  else if(name=="nusmv")
    m=new modelchecker_smvt(args, modelchecker_smvt::NUSMV, cmdline.isset("concurrency"));
  else if(name=="satmc")
    m=new modelchecker_smvt(args, modelchecker_smvt::SATMC, cmdline.isset("concurrency"));
  else if(name=="spin")
    m=new modelchecker_spint(args, cmdline.isset("concurrency"));
  else if(name=="boom")
	m=new modelchecker_boolean_programt(args, modelchecker_boolean_programt::BOOM, max_threads, cmdline.isset("concurrency"));
  else
    throw "unknown modelchecker: "+name;

  assert(m!=NULL);
    
  if(cmdline.isset("loop-detection"))
    m->enable_loop_detection();
    
  return m;
}
