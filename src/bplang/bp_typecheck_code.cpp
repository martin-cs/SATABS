/*******************************************************************\

Module: Boolean Program Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <set>

#include <expr_util.h>
#include <location.h>
#include <arith_tools.h>
#include <i2string.h>
#include <config.h>
#include <prefix.h>
#include <std_expr.h>

#include "bp_typecheck.h"

/*******************************************************************\

Function: bp_typecheckt::typecheck_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck_code(codet &code)
{
  assert(code.id()==ID_code);
  
  const irep_idt &statement=code.get_statement();
  
  if(statement==ID_label)
  {
    const irep_idt &label=code.get(ID_label);

    if(code.operands().size()!=1)
    {
      err_location(code);
      throw "label statement expects one operand";
    }
    
    typecheck_code(to_code(code.op0()));
    
    if(has_prefix(id2string(label), "ASYNC_"))
    {
      exprt start_thread(ID_code);
      start_thread.set(ID_statement, ID_start_thread);
      start_thread.move_to_operands(code.op0());
      code.op0().swap(start_thread);
    }
    #if 0
    else if(!error_label.empty() && label==error_label)
    {
      exprt assertion(ID_code);
      assertion.set(ID_statement, ID_assert);
      assertion.copy_to_operands(false_exprt());

      exprt new_block(ID_code);
      new_block.set(ID_statement, ID_block);
      new_block.move_to_operands(assertion, code.op0());
      code.op0().swap(new_block);
    }
    #endif
  }
  else if(statement==ID_ifthenelse)
  {
    typecheck_code_ifthenelse(code);
  }
  else if(statement==ID_block)
  {
    typecheck_code_block(code);
  }
  else if(statement==ID_goto)
  {
    typecheck_code_goto(code);
  }
  else if(statement==ID_bp_constrain)
  {
    typecheck_code_constrain(code);
  }
  else if(statement=="non-deterministic-goto")
  {
    typecheck_code_non_deterministic_goto(code);
  }
  else if(statement==ID_return)
  {
    typecheck_code_return(code);
  }
  else if(statement==ID_skip)
  {
    // do nothing
  }
  else if(statement==ID_decl)
  {
    typecheck_code_decl(code);
  }
  else if(statement==ID_assign)
  {
    typecheck_code_assign(code);
  }
  else if(statement==ID_bp_enforce)
  {
    typecheck_code_enforce(code);
  }
  else if(statement==ID_bp_abortif)
  {
    typecheck_code_abortif(code);
  }
  else if(statement==ID_bp_dead)
  {
    typecheck_code_dead(code);
  }
  else if(statement==ID_function_call)
  {
    typecheck_code_function_call(to_code_function_call(code));
  }
  else if(statement==ID_end_thread)
  {
    // do nothing
  }
  else if(statement==ID_sync)
  {
    // do nothing
  }
  else if(statement==ID_start_thread)
  {
    if(code.operands().size()!=1)
    {
      err_location(code);
      throw "start_thread statement expects one operand";
    }

    typecheck_code(to_code(code.op0()));
  }
  else if(statement==ID_atomic_begin)
  {
    // do nothing
  }
  else if(statement==ID_atomic_end)
  {
  }
  else
  {
    str << "bp_typecheckt: unexpected statement: "
        << code << std::endl;
    throw 0;
  }
  
}

/*******************************************************************\

Function: bp_typecheckt::typecheck_code_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck_code_assign(codet &code)
{
  if(code.operands().size()!=2)
  {
    err_location(code);
    throw "assign expects two operands";
  }

  exprt &lhs=code.op0();
  exprt &rhs=code.op1();

  if(lhs.operands().size()==0)
  {
    err_location(code);
    throw "assignment expects arguments";
  }

  Forall_operands(it, lhs)
    typecheck_expr(*it);


  if(lhs.operands().size()!=rhs.operands().size())
  {
    err_location(code);
    throw "lhs and rhs of assignment must have same number of "
          "arguments";
  }
  
  Forall_operands(it, rhs)
    typecheck_expr(*it);

  if(lhs.operands().size()==1)
  {
    // regular assignment
    
    exprt op_lhs, op_rhs;
    op_lhs.swap(lhs.op0());
    op_rhs.swap(rhs.op0());
    
    lhs.swap(op_lhs);
    rhs.swap(op_rhs);
  }
  else
  {
    // multi-assignment
    
    lhs.id("bool-vector");
    rhs.id("bool-vector");

    lhs.type().id("bool-vector");
    lhs.type().set(ID_width, lhs.operands().size());
    rhs.type()=lhs.type();
  }
}

/*******************************************************************\

Function: bp_typecheckt::typecheck_code_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck_code_function_call(code_function_callt &code)
{
  exprt &function=code.function();
  exprt &lhs=code.lhs();
  
  const irep_idt &identifier=function.get(ID_identifier);

  exprt::operandst &arguments=code.arguments();

  Forall_expr(it, arguments)
    typecheck_expr(*it);

  // built-in ones
  if(identifier==ID_assert ||
     identifier==ID_assume)
  {
    if(arguments.size()!=1)
    {
      err_location(code);
      str << identifier << " takes one argument";
      throw 0;
    }
    
    if(lhs.is_not_nil())
    {
      err_location(code);
      str << identifier << " must not have LHS";
      throw 0;
    }
    
    exprt op;
    op.swap(arguments[0]);
    
    code.set(ID_statement, identifier);
    code.operands().clear();
    code.move_to_operands(op);
    
    return;
  }

  // fix the identifier
  const irep_idt full_identifier=
    "bp::fkt::"+id2string(identifier);

  function.set(ID_identifier, full_identifier);  
  
  contextt::symbolst::iterator s_it=context.symbols.find(full_identifier);

  if(s_it==context.symbols.end())
  {
    err_location(code);
    str << "function " << identifier << " not found";
    throw 0;
  }
  
  const symbolt &symbol=s_it->second;
  
  function.type()=symbol.type;

  if(lhs.is_not_nil())
  {
    if(lhs.operands().size()==1)
    {
      // regular assignment
      exprt op_lhs;
      op_lhs.swap(lhs.op0());
      lhs.swap(op_lhs);
      typecheck_expr(lhs);
    }
    else
    {
      // multi-assignment
      lhs.id("bool-vector");
      lhs.type().id("bool-vector");
      lhs.type().set(ID_width, lhs.operands().size());

      Forall_operands(it, lhs)
        typecheck_expr(*it);
    }
    
    const typet &rhs_type=to_code_type(symbol.type).return_type();

    if(lhs.type()!=rhs_type)
    {
      err_location(code);
      str << "type mismatch in assignment:" << std::endl;
      str << "LHS: " << to_string(lhs.type()) << std::endl;
      str << "RHS: " << to_string(rhs_type);
      throw 0;
    }
  }
}

/*******************************************************************\

Function: bp_typecheckt::typecheck_code_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck_code_block(codet &code)
{
  exprt::operandst &op=code.operands();

  // split up declarations

  for(exprt::operandst::iterator it=op.begin();
      it!=op.end();) // no it++
  {
    if(it->get(ID_statement)==ID_decl &&
       it->operands().size()>=2)
    {
      exprt old_decl;
      old_decl.swap(*it);
      
      it=op.erase(it);
      
      Forall_operands(o_it, old_decl)
      {
        it=op.insert(it, exprt());
        exprt new_decl(ID_code);
        new_decl.set(ID_statement, ID_decl);
        new_decl.move_to_operands(*o_it);
        it->swap(new_decl);
      }
    }
    else
      it++;
  }

  // move code after enforce

  for(exprt::operandst::iterator it=op.begin();
      it!=op.end(); it++)
  {
    if(it->get(ID_statement)==ID_bp_enforce)
    {
      exprt &enforce=*it;
      assert(enforce.operands().size()==2);
      exprt &op1=enforce.op1();
      op1=exprt(ID_code, typet(ID_code));
      op1.set(ID_statement, ID_block);

      for(it++; it!=op.end(); it=op.erase(it))
        op1.move_to_operands(*it);
        
      break;
    }
  }

  Forall_operands(it, code)
    typecheck_code(to_code(*it));
}

/*******************************************************************\

Function: bp_typecheckt::typecheck_code_return

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck_code_return(codet &code)
{
  if(number_of_returned_variables!=code.operands().size())
  {
    err_location(code);
    throw "wrong number of return values";
  }

  Forall_operands(it, code)
    typecheck_expr(*it);
    
  if(number_of_returned_variables>=2)
  {
    exprt op("bool-vector");
    op.operands().swap(code.operands());
    op.type()=typet("bool-vector");
    op.type().set(ID_width, number_of_returned_variables);
    code.move_to_operands(op);
  }
}

/*******************************************************************\

Function: bp_typecheckt::typecheck_code_non_deterministic_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck_code_non_deterministic_goto(codet &code)
{
}

/*******************************************************************\

Function: bp_typecheckt::typecheck_code_constrain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck_code_constrain(codet &code)
{
  if(code.operands().size()!=2)
  {
    err_location(code);
    throw "constrain expects two operands";
  }
  
  exprt &assignment=code.op0();
  exprt &constraint=code.op1();
  
  typecheck_code(to_code(assignment));
  typecheck_expr(constraint);
}

/*******************************************************************\

Function: bp_typecheckt::typecheck_code_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck_code_goto(codet &code)
{
}

/*******************************************************************\

Function: bp_typecheckt::typecheck_code_enforce

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck_code_enforce(codet &code)
{
  if(code.operands().size()!=2)
  {
    err_location(code);
    throw "enforce expects two operands";
  }
  
  typecheck_expr(code.op0());
  
  typecheck_code(to_code(code.op1()));
}

/*******************************************************************\

Function: bp_typecheckt::typecheck_code_abortif

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck_code_abortif(codet &code)
{
  if(code.operands().size()!=1)
  {
    err_location(code);
    throw "abortif expects one operand";
  }
  
  typecheck_expr(code.op0());
}

/*******************************************************************\

Function: bp_typecheckt::typecheck_code_dead

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck_code_dead(codet &code)
{
}

/*******************************************************************\

Function: bp_typecheckt::typecheck_code_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck_code_decl(codet &code)
{
  assert(code.operands().size()==1);
  
  exprt &op=code.op0();
  
  op.type()=typet(ID_bool);

  symbolt symbol;

  symbol.mode=mode;
  symbol.value.make_nil();
  symbol.is_state_var=true;
  symbol.is_static_lifetime=false;
  symbol.is_lvalue=true;
  symbol.type=typet(ID_bool);

  symbol.base_name=op.get(ID_identifier);

  symbol.name=
    id2string(symbol.mode)+"::local_var::"+
    id2string(function_name)+"::"+
    id2string(symbol.base_name);

  symbol.pretty_name=
    id2string(function_name)+"::"+
    id2string(symbol.base_name);

  op.set(ID_identifier, symbol.name);
  
  context.move(symbol);
}

/*******************************************************************\

Function: bp_typecheckt::typecheck_code_ifthenelse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck_code_ifthenelse(codet &code)
{
  if(code.operands().size()!=2 &&
     code.operands().size()!=3)
  {
    err_location(code);
    throw "if-then-else statement expects two or three operands";
  }

  typecheck_expr(code.op0());
  typecheck_code(to_code(code.op1()));
  
  if(code.operands().size()==3)
    typecheck_code(to_code(code.operands()[2]));
}
