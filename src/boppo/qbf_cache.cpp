/*******************************************************************\

Module: Cache for QBF Instances

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "qbf_cache.h"

/*******************************************************************\

Function: qdimacs_cnf_hash::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

size_t qdimacs_cnf_hash::operator()(const qdimacs_cnft &qdimacs_cnf) const
{
  return qdimacs_cnf.hash();
}

/*******************************************************************\

Function: qbf_cachet::check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
qbf_cachet::statust qbf_cachet::check(const qdimacs_cnft &qdimacs_cnf) const
{
  cachet::const_iterator it=cache.find(qdimacs_cnf);

  if(it==cache.end())
    return NOT_IN_CACHE;
    
  return it->second?IS_TRUE:IS_FALSE;
}

/*******************************************************************\

Function: qbf_cachet::set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void qbf_cachet::set(const qdimacs_cnft &qdimacs_cnf, bool validity)
{
  cache.insert(std::pair<qdimacs_cnft, bool>(qdimacs_cnf, validity));
}
