/*******************************************************************\

Module: Ranking Function Synthesis Base Class

Author: CM Wintersteiger

Date: October 2008

\*******************************************************************/

#ifndef CPROVER_RANKING_BASE_H_
#define CPROVER_RANKING_BASE_H_

#include <map>
#include <set>

#include <util/message.h>
#include <util/expr.h>
#include <util/replace_expr.h>
#include <util/time_stopping.h>
#include <util/arith_tools.h>
#include <util/find_symbols.h>
#include <util/namespace.h>

#include <solvers/flattening/boolbv.h>

#include "ranking_tools.h"
#include "ranking_body.h"

class ranking_synthesis_baset:public messaget
{
protected:
  typedef find_symbols_sett intermediate_statet;

  const symbol_tablet &symbol_table;
  symbol_tablet &shadow_symbol_table;
  namespacet ns;
  const bodyt &body;
  exprt rank_relation;
  intermediate_statet intermediate_state;
  exprt largest_constant;
  unsigned largest_constant_width;
  boolbv_widtht bv_width;

  fine_timet conversion_time;
  fine_timet solver_time;
  unsigned solver_calls;

public:
  ranking_synthesis_baset(
    const bodyt &_body,
    const symbol_tablet &_ctx,
    symbol_tablet &_sctx,
    message_handlert &_mh):
    messaget(_mh),
    symbol_table(_ctx),
    shadow_symbol_table(_sctx),
    ns(_ctx, _sctx),
    body(_body),
    largest_constant_width(0),
    bv_width(ns),
    conversion_time(0),
    solver_time(0),
    solver_calls(0)
  {
    typet ctype=typet(ID_unsignedbv);
    ctype.set(ID_width, 8);
    largest_constant = from_integer(0, ctype);
  }

  virtual ~ranking_synthesis_baset() {}

  exprt ranking(void);

protected:
  find_symbols_sett used_variables;
  
  void find_largest_constant(const exprt &expr);
  void find_intermediate_state(void);
  void find_nondet_symbols(const exprt &expr, find_symbols_sett &set);

  virtual bool generate_functions(void)=0;
  virtual exprt instantiate(void)=0;

  void show_variables(void);
  void show_varmap(const boolbvt &converter, std::ostream &out) const;
  void show_mapping(const boolbvt &converter, const irep_idt &ident,
                    const typet &type, std::ostream &out) const;

  std::string print_dependencies(const exprt &expr) const;

  void cast_up(exprt &a, exprt &b) const;
};

#endif /* CPROVER_RANKING_BASE_H_ */
