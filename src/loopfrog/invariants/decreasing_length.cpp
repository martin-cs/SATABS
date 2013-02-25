/*******************************************************************\

 Module: A string length invariant

 Author: CM Wintersteiger

\*******************************************************************/

#include <std_expr.h>
#include <expr_util.h>
#include <message.h>

#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>

#include <goto-programs/string_instrumentation.h>

#include "../pointer_expr.h"
#include "../string_utils.h"

#include "decreasing_length.h"

/*******************************************************************\

 Function: decreasing_length_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose: Tests for decreasing string length

\*******************************************************************/

void decreasing_length_invariant_testt::get_invariants(
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
      pointers.push_back(*it);
    }
    else if(it->id()=="index")
    {
      if(is_string_type(ns.follow(it->op0().type())))
      {
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
    std::cout << "DL TEST: " << expr2c(*it, ns) << std::endl;
    #endif

    symbol_exprt temporary = get_temporary_symbol(uint_type());

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
    
    if(zero_length.op0().id()=="dereference" &&
       zero_length.op0().op0().id()=="constant" &&
       zero_length.op0().get("value")=="NULL") continue; // not necessary...

    exprt buf_size = ::buffer_size(temp);

    binary_relation_exprt leqt(zero_length, "<=", temp);
    binary_relation_exprt leqb(temp, "<=", buf_size);

    and_exprt invariant(leqt, leqb);
    invariant.set("#unconditional", true);
    potential_invariants.insert(invariant);

    #if 0
    std::cout << "DL INVARIANT: " << expr2c(invariant, ns) << std::endl;
    #endif
  }
}
