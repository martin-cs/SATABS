/*******************************************************************\

Module: Boolean Program Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include "bp_typecheck.h"

/*******************************************************************\

Function: bp_typecheckt::typecheck_boolean_operands

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck_boolean_operands(exprt &expr)
{
  if(expr.operands().size()==0)
  {
    err_location(expr);
    str << "Expected operands for " << expr.id_string()
        << " operator";
    throw 0;
  }

  Forall_operands(it, expr)
    typecheck_expr(*it);

  expr.type()=typet(ID_bool);

  forall_operands(it, expr)
    if(it->type().id()!=ID_bool)
    {
      err_location(*it);
      str << "Expected Boolean operands for " << expr.id_string()
          << " operator";
      throw 0;
    }
}

/*******************************************************************\

Function: bp_typecheckt::typecheck_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck_expr(exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);

    if(identifier=="T")
      expr.make_true();
    else if(identifier=="F")
      expr.make_false();
    else if(identifier=="_")
    {
      expr.id("bp_unused");
      expr.remove(ID_identifier);
    }
    else
    {
      irep_idt full_identifier;
      
      // first try local variable
      full_identifier=
        "bp::local_var::"+
        id2string(function_name)+"::"+
        id2string(identifier);

      contextt::symbolst::iterator s_it=context.symbols.find(full_identifier);

      if(s_it==context.symbols.end())
      {
        // try function argument next
        full_identifier=
          "bp::argument::"+id2string(function_name)+"::"+
          id2string(identifier);

        s_it=context.symbols.find(full_identifier);

        if(s_it==context.symbols.end())
        {
          // try global next
          full_identifier="bp::var::"+id2string(identifier);

          s_it=context.symbols.find(full_identifier);

          if(s_it==context.symbols.end())
          {
            err_location(expr);
            str << "variable `" << identifier << "' not found";
            throw 0;
          }
        }
      }

      symbolt &symbol=s_it->second;

      expr.type()=symbol.type;
      expr.set(ID_identifier, full_identifier);
    }
  }
  else if(expr.id()==ID_nondet_bool)
  {
    expr.type()=typet(ID_bool);
  }
  else if(expr.id()==ID_next_symbol)
  {
    if(expr.operands().size()!=1)
    {
      err_location(expr);
      throw "tick operator expects one operand";
    }

    exprt &op=expr.op0();
    
    typecheck_expr(op);

    if(op.id()!=ID_symbol)
    {
      err_location(expr);
      throw "tick operator expects a symbol as operand";
    }
    
    exprt tmp;
    
    tmp.swap(op);
    tmp.id(ID_next_symbol);
    
    expr.swap(tmp);
  }
  else if(expr.id()==ID_bp_schoose)
  {
    typecheck_boolean_operands(expr);
    
    // Must have two arguments.
    // The first one is for "result must be true",
    // the second for "result must be false"
    // schoose[a,b] is like (* and !b) | a
    
    if(expr.operands().size()!=2)
    {
      err_location(expr);
      throw "schoose takes two arguments";
    }
    
    if(expr.op0().is_true())
    {
      // schoose[T,F] means "must be true and not false"
      // schoose[T,T] means "must be true and false"
      // in Moped, the later happens to be true
      expr.make_true();
    }
    else if(expr.op1().is_true())
    {
      // schoose[x,T] is x
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
    }
    else if(expr.op0().is_false() &&
            expr.op1().is_false())
    {
      // schoose[F,F] is true non-deterministic choice
      expr.id(ID_nondet_bool);
      expr.operands().clear();
    }
    else if(expr.op1().is_false())
    {
      // schoose[x,T] is * | x

      exprt nondet(ID_nondet_bool, typet(ID_bool));
      exprt or_expr(ID_or, typet(ID_bool));
      or_expr.move_to_operands(nondet, expr.op0());
      expr.swap(or_expr);
    }
    else if(expr.op1().id()==ID_not &&
            expr.op1().operands().size()==1 &&
            expr.op1().op0()==expr.op0())
    {
      // schoose[a,!a]==a
      exprt tmp;
      tmp.swap(expr.op0());
      expr.swap(tmp);
    }
    else // Variables involved...
    {
      // build (* and !b) | a
      exprt nondet(ID_nondet_bool, typet(ID_bool));
      exprt not_op1(ID_not, typet(ID_bool));
      not_op1.move_to_operands(expr.op1());
      exprt and_expr(ID_and, typet(ID_bool));
      and_expr.move_to_operands(nondet, not_op1);
      exprt or_expr(ID_or, typet(ID_bool));
      or_expr.move_to_operands(and_expr, expr.op0());
      expr.swap(or_expr);
    }
  }
  else if(expr.id()==ID_and || expr.id()==ID_or ||
          expr.id()==ID_xor || expr.id()==ID_not ||
          expr.id()==ID_implies ||
          expr.id()==ID_equal || expr.id()==ID_notequal)
  {
    typecheck_boolean_operands(expr);
  }
  else if(expr.id()==ID_constant)
  {
    const irep_idt &value=expr.get(ID_value);
    
    if(value==ID_0)
    {
      expr.make_false();
    }
    else if(value==ID_1)
    {
      expr.make_true();
    }
    else
    {
      err_location(expr);
      str << "Invalid constant: " << value;
      throw 0;
    }
  }
  else if(expr.id()==ID_sideeffect)
  {
    //const irep_idt &statement=expr.get("statement");

    err_location(expr);
    str << "No type checking for sideeffect " << expr;
    throw 0;
  }
  else
  {
    err_location(expr);
    str << "No type checking for " << expr;
    throw 0;
  }
}
