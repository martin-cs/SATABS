/*******************************************************************\

Module: Refiner Selection

Authors: Daniel Kroening, daniel.kroening@inf.ethz.ch

Date: September 2005

\*******************************************************************/

#include "select_refiner.h"
#include "refiner_wp.h"
#include "refiner_lifter.h"
#include "no_refiner.h"

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
  const cmdlinet &cmdline,
  const loop_componentt::argst &args)
{
  unsigned max_predicates_to_add;
  if(cmdline.isset("max-new-predicates"))
  {
	  max_predicates_to_add = atoi(cmdline.getval("max-new-predicates"));
  } else {
	  max_predicates_to_add = (unsigned)(-1);
  }
  bool prefer_non_pointer_predicates = cmdline.isset("prefer-non-pointer-predicates");

  std::string name=
    cmdline.isset("refiner")?cmdline.getval("refiner"):"wp";
    
  bool prefix_first=cmdline.isset("prefix-first");

  if(name=="wp")
    return new refiner_wpt(args, prefix_first, max_predicates_to_add, prefer_non_pointer_predicates);
  else if(name=="ipp")
  {
    #ifdef HAVE_IPP
    int limit =
      cmdline.isset("ipplimit") ?atoi(cmdline.getval("ipplimit")) : -1;
    // -1 means use unsplit prover
    return new refiner_ippt(args, prefix_first, limit, max_predicates_to_add, prefer_non_pointer_predicates);
    #else
    throw "support for IPP not linked in";
    #endif
  }
  else if(name=="lifter")
    return new refiner_liftert(args, prefix_first, max_predicates_to_add, prefer_non_pointer_predicates);
  else if(name=="none")
    return new no_refinert(args);
  else if(name=="transitions_only")
    return new transition_refinert(args, false, max_predicates_to_add, prefer_non_pointer_predicates);
  else
    throw "unknown refiner: "+name;
}
