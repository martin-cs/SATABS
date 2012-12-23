/*******************************************************************\

Module: 

Author: CM Wintersteiger

\*******************************************************************/

#include <arith_tools.h>
#include <i2string.h>

#include "ranking_tools.h"
#include "expr2seneschal.h"

/*******************************************************************\

 Function: expr2seneschalt::convert_rec

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

std::string expr2seneschalt::convert_rec(
  const exprt &e, 
  bool negated, 
  bool bool_context)
{
  std::string res;

  if(e.id()==ID_symbol)
  {
    if(bool_context)
      return e.get_string(ID_identifier) + "=" + ((negated)?"0":"1");
    else
      return e.get_string(ID_identifier);
  }
  else if(e.id()==ID_constant)
  {
    mp_integer mi;
    to_integer(e, mi);
    
    if(bool_context)
    {
      if(mi==0)
        return "false";
      else
        return "true";
    }
    else
      return integer2string(mi);
  }
  else if(e.id()==ID_equal || e.id()==ID_notequal ||
          e.id()==ID_lt || e.id()==ID_gt ||
          e.id()==ID_le || e.id()==ID_ge)
  {
    assert(e.operands().size()==2);
    std::string op = e.id()==ID_notequal ? "!=" : e.id_string();
    
    if(bool_context && negated)
    {
      if(op=="=") op="!=";
      else if(op=="!=") op="=";
      else if(op=="<") op=">=";
      else if(op==">") op="<=";
      else if(op=="<=") op=">";
      else if(op==">=") op="<";
      else throw std::string("Unknown OP:") + op;
    }
    
    if(!bool_context)
    {
      if(op=="=")
        return "equals("+convert_rec(e.op0())+", "+convert_rec(e.op1())+")";
      if(op=="!=")
        return "not(equals("+convert_rec(e.op0())+", "+convert_rec(e.op1())+"))";
      else
        throw std::string("Missing Arith-1 Function: ") + op;
    }
    else
      return "(" + convert_rec(e.op0()) + " " + op + " " + convert_rec(e.op1())+")";
  }
  else if(e.id()==ID_not)
  {
    assert(e.operands().size()==1);
    unsigned w=safe_width(e, ns);
    
    if(bool_context || w==1)
      return std::string("(") + convert_rec(e.op0(), !negated, true) + ")";
    else
    {
      std::string res("bitneg"); 

      if(e.type().id()==ID_unsignedbv || e.type().id()==ID_bool)
        res+="U";
      
      res += i2string(w) + "(" + convert_rec(e.op0()) + ")";
      return res;
    }
  }
  else if(e.id()==ID_if && bool_context)
  {
    assert(e.operands().size()==3);
        
    return std::string("((") + convert_rec(e.op0(), false, true) + " & " + 
                               convert_rec(e.op1(), negated, true) + ") | (" +
                               convert_rec(e.op0(), true, true) + " & " + 
                               convert_rec(e.op2(), negated, true) + "))";
  }
  else if(e.id()==ID_plus || e.id()==ID_minus || e.id()==ID_mult || 
          e.id()==ID_div || e.id()==ID_mod ||
          e.id()==ID_bitand || e.id()==ID_bitor || e.id()==ID_bitxor)
  {
    assert(e.operands().size()>=2);
    assert(!bool_context);

    unsigned w=safe_width(e, ns);
    std::string op = e.id()==ID_plus   ? "add" :
                     e.id()==ID_minus  ? "sub" :
                     e.id()==ID_mult   ? "mul" :
                     e.id()==ID_div    ? "div" :
                     e.id()==ID_mod    ? "mod" :
                     e.id()==ID_bitand ? "and" : 
                     e.id()==ID_bitor  ? "or"  : 
                                         "xor";
    
    if(op=="add" || op=="sub" || op=="mul" || op=="div")
    {
      if(e.type().id()=="unsignedbv" || e.type().id()=="bool")
        op+="U";
    
      op += i2string(w);
    }

    std::string last;   
    forall_operands(it, e)
    {
      if(it==e.operands().begin())
      {
        exprt::operandst::const_iterator last_it = it;
        it++;
        
        last = op + "(" + convert_rec(*last_it, negated) + "," + 
                          convert_rec(*it, negated) + ")";
      }
      else
        last = op + "(" + last + "," + convert_rec(*it, negated) + ")";
    }
    
    return last;
  }
  else if(e.id()==ID_unary_minus || e.id()==ID_bitnot)
  {
    assert(e.operands().size()==1);
    assert(!bool_context);
    
    std::string op = (e.id()==ID_unary_minus) ? "minus" : "bitneg";
    unsigned w=safe_width(e, ns);
    
    return op + 
           ((e.type().id()==ID_unsignedbv)?"U":"") + i2string(w) +
           "(" + convert_rec(e.op0(), negated) + ")";
  }
  else if(e.id()==ID_lshr || e.id()==ID_shl)
  {
    assert(e.operands().size()==2);
    assert(!bool_context);
    
    unsigned w=safe_width(e, ns);
    
    return std::string("shift") + 
           ((e.type().id()==ID_unsignedbv)?"U":"") + i2string(w) +
           "(" + convert_rec(e.op0(), negated) + ", " + 
           ((e.id()==ID_lshr)?"-":"") + convert_rec(e.op1(), negated) + ")";
  }
  else if(e.id()==ID_and || e.id()==ID_or)
  {
    assert(e.operands().size()>=2);
    assert(bool_context);

    std::string res;
    forall_operands(it, e)
    {
      if(it==e.operands().begin())
        res = "(" + convert_rec(*it, negated, true);
      else
        res += ((e.id()==ID_and)?" & ":" | ") + convert_rec(*it, negated, true);
    }
    return res+")";
  }
  else if(e.id()==ID_typecast)
  {
    assert(e.operands().size()==1);   
    unsigned w=safe_width(e, ns);
    
    if(bool_context || w==1)
      return convert_rec(e.op0()) + ((negated)?"!":"") + "=0";
    else
    {     
      return std::string("cast") + 
              ((e.type().id()==ID_unsignedbv || e.type().id()==ID_bool)?"U":"") + 
               i2string(w) + "(" + convert_rec(e.op0(), negated, false) + ")";
    }
  }
  else if(e.id()=="seneschal-range")
  {
    assert(e.operands().size()==1);
    return e.type().id_string() + "(" + convert_rec(e.op0(), negated) + ")";
  }
  else
    throw UnhandledException(e);
}
