/*******************************************************************\

Module: Custom bitvector-rankfunction typechecker

Author: CM Wintersteiger

Date: May 2009

\*******************************************************************/

#ifndef RANKFUNCTION_TYPECHECK_H_
#define RANKFUNCTION_TYPECHECK_H_

#include <util/typecheck.h>
#include <util/symbol_table.h>
#include <util/namespace.h>
#include <util/message.h>

#include <ansi-c/ansi_c_parse_tree.h>

bool parse_rank_function(const std::string &code, symbol_tablet &symbol_table,
                         const namespacet &ns, message_handlert &mh, exprt &rf);

class rankfunction_typecheckt:public typecheckt
{
public:
  rankfunction_typecheckt(
    ansi_c_parse_treet &_parse_tree,
    symbol_tablet &_symbol_table,
    const namespacet &_ns,
    message_handlert &_message_handler):
      typecheckt(_message_handler),
      parse_tree(_parse_tree),
      ns(_symbol_table),
      ext_ns(_ns)
  {
  }

  virtual ~rankfunction_typecheckt(void) { }

  virtual void typecheck(void)
  {
    throw ("N/A"); // This is only meant for expr's
  }

  virtual void typecheck_expr(exprt &expr);

protected:
  ansi_c_parse_treet &parse_tree;
  namespacet ns;
  namespacet ext_ns;
};


#endif /* RANKFUNCTION_TYPECHECK_H_ */
