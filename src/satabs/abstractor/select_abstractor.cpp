/*******************************************************************\

Module: Abstractor Selection

Authors: Daniel Kroening, kroening@kroening.com

Date: September 2005

\*******************************************************************/

#include <cstdlib>

#include "select_abstractor.h"
#include "abstractor_wp.h"
#include "abstractor_satqe.h"
#include "abstractor_prover.h"
#include "abstractor_wp_cartesian.h"
#include "concurrency_aware_abstractor.h"

#include <string2int.h>

/*******************************************************************\

Function: select_abstractor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

abstractort *select_abstractor(
  const cmdlinet &cmdline,
  const loop_componentt::argst &args,
  const goto_functionst &functions)
{
  std::string name=
    cmdline.isset("abstractor")?cmdline.getval("abstractor"):"wp";

  abstractort * specific_abstractor = NULL;

  if(name=="wp")
	specific_abstractor = new abstractor_wpt(args);
  else if(name=="prover")
    #ifdef HAVE_PROVER
	specific_abstractor = new abstractor_provert(args);
    #else
    throw "support for prover not linked in";
    #endif
  else if(name=="satqe")
    #ifdef HAVE_SATQE
    specific_abstractor = new abstractor_satqet(args);
    #else
    throw "support for satqe not linked in";
    #endif
  else if(name=="cartesian")
  {
    const unsigned int max_cube_length = cmdline.isset("max-cube-length")?safe_str2unsigned(cmdline.getval("max-cube-length")):3;
    specific_abstractor = new abstractor_wp_cartesiant(args, max_cube_length, functions);
  }
  else
    throw "unknown abstractor: "+name;

  if(cmdline.isset("concurrency"))
  {
	  return new concurrency_aware_abstractort(
        args,
        std::auto_ptr<abstractort>(specific_abstractor),
        functions,
        cmdline.isset("passive-nondet"));
  } else {
	  return specific_abstractor;
  }

}
