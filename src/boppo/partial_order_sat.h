/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PARTIAL_ORDER_SAT_H
#define CPROVER_PARTIAL_ORDER_SAT_H

#include <propdec/satcheck_zchaff.h>

class partial_order_satt:public satcheck_zchaff_baset
{
 public:
  partial_order_satt();
  virtual ~partial_order_satt();
  
 protected:
  class partial_order_solvert *solver_ptr;
}; 

#endif
