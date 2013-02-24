/*******************************************************************

 Module: A string length preservation invariant

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_STRING_LENGTH_H_
#define __CPROVER_LOOPFROG_INVARIANTS_STRING_LENGTH_H_

#include "invariant_test.h"

class string_length_invariant_testt : 
  public invariant_testt
{
public:
  string_length_invariant_testt(
    contextt &context) : 
      invariant_testt("SL", "String Length", context) {}
  
  virtual ~string_length_invariant_testt(void) {}
  
  virtual void get_invariants(
    const loop_summaryt &summary,
    std::set<exprt> &potential_invariants);
  
};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_STRING_LENGTH_H_*/
