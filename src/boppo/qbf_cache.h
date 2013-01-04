/*******************************************************************\

Module: Cache for QBF Instances

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BOPPO_QBF_CACHE_H
#define CPROVER_BOPPO_QBF_CACHE_H

#include <hash_cont.h>

#include <solvers/qbf/qdimacs_cnf.h>

struct qdimacs_cnf_hash
{
  size_t operator()(const qdimacs_cnft &qdimacs_cnf) const;
};
  
class qbf_cachet
{
public:
  typedef enum { IS_TRUE, IS_FALSE, NOT_IN_CACHE } statust;

  statust check(const qdimacs_cnft &qdimacs_cnf) const;
  
  void set(const qdimacs_cnft &qdimacs_cnf, bool validity);

protected:
  typedef hash_map_cont<qdimacs_cnft, bool, qdimacs_cnf_hash> cachet;
  cachet cache;
};

#endif
