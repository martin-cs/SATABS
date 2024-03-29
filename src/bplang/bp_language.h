/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BP_LANGUAGE_H
#define CPROVER_BP_LANGUAGE_H

#include <util/language.h>

#include "bp_parse_tree.h"

class bp_languaget:public languaget
{
public:
  virtual std::string id() const { return "bp"; }
  virtual std::string description() const { return "Boolean Programs"; }
  virtual std::set<std::string> extensions() const
  { std::set<std::string> s; s.insert("bp"); return s; }  
  
  virtual bool parse(
    std::istream &instream,
    const std::string &path);

  virtual void modules_provided(std::set<std::string> &module_set);
                 
  virtual bool typecheck(
    symbol_tablet &symbol_table,
    const std::string &module);
  
  virtual bool final(
    symbol_tablet &symbol_table);
  
  virtual void show_parse(std::ostream &out);
  
  virtual ~bp_languaget() { }
  
  virtual bool from_expr(
    const exprt &expr,
    std::string &code,
    const namespacet &ns);

  virtual bool from_type(
    const typet &type,
    std::string &code,
    const namespacet &ns);

  virtual bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns);
                       
  virtual languaget *new_language()
  { return new bp_languaget; }
     
  bp_parse_treet bp_parse_tree;
};

languaget *new_bp_language();
 
#endif
