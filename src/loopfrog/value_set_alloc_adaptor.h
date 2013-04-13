/*******************************************************************

 Module: Adaptor for value sets (dynamic object removal)

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_LOOPFORG_VALUE_SET_ALLOC_ADAPTOR_H_
#define _CPROVER_LOOPFORG_VALUE_SET_ALLOC_ADAPTOR_H_

#include <util/expr_util.h>
#include <util/symbol_table.h>

#include <pointer-analysis/value_sets.h>

class value_set_alloc_adaptort : public value_setst
{
private:
  symbol_tablet &symbol_table;
  value_setst &value_sets;

public:
  value_set_alloc_adaptort(
    symbol_tablet &_symbol_table,
    value_setst &_value_sets) :
      symbol_table(_symbol_table),
      value_sets(_value_sets) {};

  virtual void get_values(
      goto_programt::const_targett l,
      const exprt &expr,
      valuest &dest);

private:
  void replace_dynamic_objects(exprt &expr);
};

#endif /*_CPROVER_LOOPFORG_VALUE_SET_ALLOC_ADAPTOR_H_*/
