/*******************************************************************\

Module: 

Author: CM Wintersteiger

\*******************************************************************/

#ifndef EXPR2SENESCHAL_H_
#define EXPR2SENESCHAL_H_

#include <util/expr.h>
#include <util/namespace.h>

class expr2seneschalt
{
protected:
  const namespacet &ns;
 
public:
  explicit expr2seneschalt(const namespacet &_ns) : ns(_ns) {}
  ~expr2seneschalt() {}

  class UnhandledException
  {
  public:
    exprt reason;
    explicit UnhandledException(exprt r) : reason(r) {};
  };

  std::string operator()(const exprt &e, 
                         bool negated=false, 
                         bool bool_context=false)
  {
    return convert_rec(e, negated, bool_context);
  }

protected:
  std::string convert_rec(const exprt &e, 
                          bool negated=false, 
                          bool bool_context=false);
};

#endif
