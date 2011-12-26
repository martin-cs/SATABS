/*******************************************************************\

Module: Transition Cache

Author: Daniel Kroening
    
Date: October 2005

Purpose:

\*******************************************************************/

#ifndef CPROVER_SATABS_REFINER_TRANSITION_CACHE_H
#define CPROVER_SATABS_REFINER_TRANSITION_CACHE_H

#include "../modelchecker/abstract_counterexample.h"

class transition_cachet
{
public:
  //typedef std::map<unsigned, bool> valuest;
  typedef std::vector<bool> valuest;

  struct entryt
  {
    goto_programt::const_targett pc;
    valuest from, to;
    valuest from_passive, to_passive;

    friend bool operator==(
      const entryt &a,
      const entryt &b)
    {
      if(a.pc!=b.pc)
        return false;
      
      return a.from==b.from && a.to==b.to &&
        a.from_passive==b.from_passive &&
        a.to_passive==b.to_passive;
    }
    
    void build(
      const abstract_stept &abstract_state_from,
      const abstract_stept &abstract_state_to,
      unsigned passive_id);
  };

  struct entry_hasht
  {
    size_t operator()(const entryt &e) const
    {
      return ((unsigned long)&(*e.pc))^e.from.size()^e.to.size()
        ^e.from_passive.size()^e.to_passive.size();
    }
  };
  
  typedef hash_set_cont<entryt, entry_hasht> cachet;
  cachet cache;

  bool in_cache(const entryt &entry)
  {
    return cache.find(entry)!=cache.end();
  }
  
  void insert(const entryt &entry)
  {
    cache.insert(entry);
  }
};

#endif
