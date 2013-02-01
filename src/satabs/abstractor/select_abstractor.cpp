/*******************************************************************\

Module: Abstractor Selection

Authors: Daniel Kroening, kroening@kroening.com

Date: September 2005

\*******************************************************************/

#include <options.h>

#include "select_abstractor.h"
#include "abstractor_wp.h"
#include "abstractor_satqe.h"
#include "abstractor_prover.h"
#include "abstractor_wp_cartesian.h"
#include "concurrency_aware_abstractor.h"

/*******************************************************************\

Function: select_abstractor

Inputs:

Outputs:

Purpose:

\*******************************************************************/

abstractort *select_abstractor(
  const optionst &options,
  const loop_componentt::argst &args)
{
  const std::string name=options.get_option("abstractor");

  abstractort *specific_abstractor=0;

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
    specific_abstractor =
      new abstractor_wp_cartesiant(args,
          options.get_int_option("max-cube-length"));
  else
    throw "unknown abstractor: "+name;

  if(options.get_bool_option("concurrency"))
  {
    return new concurrency_aware_abstractort(
        args,
        std::auto_ptr<abstractort>(specific_abstractor),
        options.get_bool_option("passive-nondet"));
  }
  else
    return specific_abstractor;
}
