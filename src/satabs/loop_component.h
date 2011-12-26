/*******************************************************************\

Module: CEGAR Loop

Author: Daniel Kroening
    
Date: May 2006

Purpose: 

\*******************************************************************/

#ifndef CPROVER_SATABS_LOOP_COMPONENT_H
#define CPROVER_SATABS_LOOP_COMPONENT_H

#include <message.h>
#include <namespace.h>

#include "prepare/concrete_model.h"

class loop_componentt:public messaget
{
public:
  struct argst
  {
    message_handlert &message_handler;
    const concrete_modelt &concrete_model;
    
    argst(
      message_handlert &_message_handler,
      const concrete_modelt &_concrete_model):
      message_handler(_message_handler),
      concrete_model(_concrete_model)
    {
    } 
  };

  loop_componentt(const argst &args):
    messaget(args.message_handler),
    concrete_model(args.concrete_model)
  {
  }

  struct statt
  {
    bool is_max;
    float val;

    statt() :
      is_max(false), val(0)
    {
    }

    statt(bool _is_max,
        float _val) :
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
      os << it->first << ": " << it->second.val << std::endl;

    return os;
  }

protected:
  const concrete_modelt &concrete_model;
};

#endif
