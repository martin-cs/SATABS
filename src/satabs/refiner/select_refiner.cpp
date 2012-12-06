/*******************************************************************\

Module: Refiner Selection

Authors: Daniel Kroening, daniel.kroening@inf.ethz.ch

Date: September 2005

\*******************************************************************/

#include <cstdlib>

#include <string2int.h>

#include "select_refiner.h"
#include "refiner_wp.h"
#include "refiner_lifter.h"
#include "no_refiner.h"
#include "refiner_wp_only.h"

#ifdef HAVE_IPP
#include "refiner_ipp.h"
#endif

/*******************************************************************\

Function: select_refiner

Inputs:

Outputs:

Purpose:

\*******************************************************************/

refinert *select_refiner(
    const optionst &options,
    const loop_componentt::argst &args)
{
  const std::string name=options.get_option("refiner");

  if(name=="wp_only")
    return new refiner_wp_onlyt(options, args);
  else if(name=="wp")
    return new refiner_wpt(options, args);
  else if(name=="ipp")
  {
#ifdef HAVE_IPP
    return new refiner_ippt(options, args);
#else
    throw "support for IPP not linked in";
#endif
  }
  else if(name=="lifter")
    return new refiner_liftert(options, args);
  else if(name=="none")
    return new no_refinert(options, args);
  else if(name=="transitions_only")
    return new transition_refinert(options, args, true);
  else
    throw "unknown refiner: "+name;
}
