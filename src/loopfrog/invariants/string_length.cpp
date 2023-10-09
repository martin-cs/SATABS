/*******************************************************************\

 Module: A string length preservation invariant

 Author: CM Wintersteiger

\*******************************************************************/

#include <iostream>

#include <util/std_expr.h>
#include <util/expr_util.h>
#include <util/message.h>

#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>

#include <goto-programs/string_instrumentation.h>

#include "../string_utils.h"
#include "string_length.h"

/*******************************************************************\
 
 Function: string_length_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose: Tests for zero termination preservation

\*******************************************************************/

void string_length_invariant_testt::get_invariants(
  const loop_summaryt &summary,
  std::set<exprt> &potential_invariants)  
{
  namespacet ns(context);
  
  stream_message_handlert mh(std::cout);
     
  std::list<exprt> pointers;
  
  // find some strings
  for(std::set<exprt>::const_iterator it=summary.variant.begin();
      it!=summary.variant.end();
      it++)
  {    
    if(is_string_type(ns.follow(it->type())))
    {      
//      std::cout << expr2c(abs.is_zero_string(*it, false, locationt()), ns) << std::endl;
//      std::cout << *it << std::endl;
      pointers.push_back(*it);
    }
    else if(it->id()=="index")
    {      
      if(is_string_type(ns.follow(it->op0().type())))
      {
//        std::cout << expr2c(abs.buffer_termination(it->op0(), locationt()), ns) << std::endl;
//        std::cout << it->op0() << std::endl;
        pointers.push_back(it->op0());
      }
    }
  }
  
  // test the invariant for every string
  for(std::list<exprt>::const_iterator it = pointers.begin();
      it!=pointers.end();
      it++)
  {
    #if 0
    std::cout << "SL TEST: " << expr2c(*it, ns) << std::endl;
    #endif
    
    exprt temp = *it;
    if(ns.follow(it->type()).id()=="array")
    {
      index_exprt array_0;
      array_0.array()=temp;
      array_0.index()=gen_zero(uint_type());
      exprt aof = address_of_exprt(array_0);
      temp.swap(aof);
    }
    
    exprt zero_length = zero_string_length(temp, false);
    
    if(zero_length.op0().op0().id()=="dereference" &&
       zero_length.op0().op0().op0().id()=="constant" &&
       zero_length.op0().op0().op0().get("value")=="NULL") continue; // not necessary...
    
    exprt buffer_size = ::buffer_size(temp);
    
    exprt invariant = binary_relation_exprt(zero_length, "<", buffer_size);
    potential_invariants.insert(invariant);
    
    #if 0
    std::cout << "SL INVARIANT: " << expr2c(invariant, ns) << std::endl;
    #endif
  }
}
