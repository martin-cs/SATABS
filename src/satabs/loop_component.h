/*******************************************************************\

Module: CEGAR Loop Component

Author: Daniel Kroening

Date: May 2006

Purpose: 

\*******************************************************************/

#ifndef CPROVER_SATABS_LOOP_COMPONENT_H
#define CPROVER_SATABS_LOOP_COMPONENT_H

#include <util/message.h>

class concrete_modelt;

class loop_componentt:public messaget
{
public:
  // Must call before use.
  virtual void set_concrete_model(const concrete_modelt &_concrete_model)
  {
    concrete_model=&_concrete_model;
  }

  struct statt
  {
    bool is_max;
    float val;

    statt():is_max(false), val(0)
    {
    }

    statt(bool _is_max, float _val):
      is_max(_is_max), val(_val)
    {
    }
  };

  typedef std::map<std::string, statt> statst;
  statst stats;

  virtual std::ostream& statistics(std::ostream &os) const
  {
    for(statst::const_iterator it=stats.begin();
        it!=stats.end();
        ++it)
      os << it->first << ": " << it->second.val << '\n';

    return os;
  }
  
protected:
  const concrete_modelt *concrete_model;
};

#endif
