/*******************************************************************\

 Module: A string tracker invariant

 Author: CM Wintersteiger

\*******************************************************************/

#include <iostream>

#include <util/std_expr.h>
#include <util/expr_util.h>
#include <util/message.h>

#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>

#include <goto-programs/string_instrumentation.h>

#include "../pointer_expr.h"
#include "../string_utils.h"

#include "constant_tracker.h"

/*******************************************************************\

 Function: constant_tracker_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose: Tests for preservation of the string tracker structure

\*******************************************************************/

void constant_tracker_invariant_testt::get_invariants(
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
    if(it->type().id()=="pointer" &&
       is_char_type(it->type().subtype()))
    {
      pointers.push_back(*it);
    }
  }

  #if 0
  // commented out due to get_string_struct()
  typet struct_ptr_type(ID_pointer);
  struct_ptr_type.subtype() = abs.get_string_struct();

  // test the invariant for every string
  for(std::list<exprt>::const_iterator it = pointers.begin();
      it!=pointers.end();
      it++)
  {
    #if 0
    std::cout << "CT TEST: " << expr2c(*it, ns) << std::endl;
    #endif

    symbol_exprt temp = get_temporary_symbol(struct_ptr_type);

    exprt bufsize = is_zero_string(*it, false);

    assert(bufsize.id()=="member");

    exprt &tracker = bufsize.op0();

    if(tracker.id()=="dereference")
    {
      exprt temp;
      temp.swap(tracker.op0());
      tracker.swap(temp);
    }

    if(tracker.is_constant() &&
       tracker.get("value")=="NULL") continue;

    binary_relation_exprt invariant(temp, "=", tracker);

    invariant.set("#unconditional", true);
    potential_invariants.insert(invariant);

    #if 0
    std::cout << "CT INVARIANT: " << expr2c(invariant, ns) << std::endl;
    #endif
  }
  #endif
}
