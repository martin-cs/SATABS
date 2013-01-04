/*******************************************************************\

Module: Boolean Program Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <cstdlib>
#include <set>

#include <expr_util.h>
#include <location.h>
#include <arith_tools.h>
#include <i2string.h>

#include "bp_typecheck.h"
#include "expr2bp.h"
#include "bp_util.h"

/*******************************************************************\

Function: bp_typecheckt::convert_declaration

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::convert_declaration(exprt &declaration)
{
  if(declaration.id()=="function")
    convert_function(declaration);
  else if(declaration.id()=="variable")
    convert_variable(declaration);
  else
    assert(0);
}

/*******************************************************************\

Function: bp_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string bp_typecheckt::to_string(const exprt &expr)
{
  return expr2bp(expr);
}

/*******************************************************************\

Function: bp_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string bp_typecheckt::to_string(const typet &type)
{
  return type2bp(type);
}

/*******************************************************************\

Function: bp_typecheckt::convert_variable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::convert_variable(exprt &declaration)
{
  symbolt symbol;
  
  symbol.mode=mode;
  symbol.value.make_nil();
  symbol.is_state_var=true;
  symbol.is_static_lifetime=true;
  symbol.is_lvalue=true;
  symbol.type=typet(ID_bool);

  forall_operands(it, declaration)
  {
    symbol.base_name=it->get(ID_identifier);

    symbol.name=
      id2string(symbol.mode)+"::var::"+id2string(symbol.base_name);

    symbol.pretty_name=symbol.base_name;
    symbol.location=it->location();

    context.add(symbol);
  }
}

/*******************************************************************\

Function: bp_typecheckt::convert_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::convert_function(exprt &declaration)
{
  symbolt symbol;

  symbol.mode=mode;

  symbol.type=typet(ID_code);
  symbol.type.add(ID_arguments).swap(declaration.add(ID_arguments));
  typet &return_type=(typet &)symbol.type.add(ID_return_type);
  return_type.swap(declaration.add(ID_return_type));

  if(return_type.id()=="bool-vector" &&
     atoi(return_type.get(ID_width).c_str())==1)
    return_type=typet(ID_bool);

  symbol.base_name=declaration.get(ID_identifier);

  symbol.name=
    id2string(symbol.mode)+"::fkt::"+
    id2string(symbol.base_name);

  symbol.value.swap(declaration.add(ID_body));
  
  convert_function_arguments(symbol);
  function_identifiers.push_back(symbol.name);  

  context.move(symbol);
}

/*******************************************************************\

Function: bp_typecheckt::convert_function_arguments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::convert_function_arguments(symbolt &fkt_symbol)
{
  irept &arguments=fkt_symbol.type.add(ID_arguments);

  symbolt arg_symbol;

  arg_symbol.mode=mode;
  arg_symbol.value.make_nil();
  arg_symbol.is_state_var=true;
  arg_symbol.is_static_lifetime=false;
  arg_symbol.is_lvalue=true;
  arg_symbol.type=typet(ID_bool);

  Forall_irep(it, arguments.get_sub())
  {
    arg_symbol.base_name=it->get(ID_identifier);
    arg_symbol.name=
      id2string(arg_symbol.mode)+"::argument::"+
      id2string(fkt_symbol.base_name)+"::"+
      id2string(arg_symbol.base_name);
    
    arg_symbol.location=((const exprt &)*it).location();

    exprt argument(ID_argument, arg_symbol.type);
    
    argument.set(ID_C_identifier, arg_symbol.name);
    argument.set(ID_C_base_name, arg_symbol.base_name);
    argument.location()=((const exprt &)*it).location();
   
    it->swap(argument);

    context.add(arg_symbol);
  }
}

/*******************************************************************\

Function: bp_typecheckt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::convert(bp_parse_treet::declarationst &declarations)
{
  Forall_expr_list(it, declarations)
    convert_declaration(*it);
}

/*******************************************************************\

Function: bp_typecheckt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bp_typecheckt::typecheck()
{
  convert(bp_parse_tree.declarations);

  // do code in functions afterwards
  
  for(std::list<irep_idt>::const_iterator
      it=function_identifiers.begin();
      it!=function_identifiers.end();
      it++)
  {
    contextt::symbolst::iterator s_it=context.symbols.find(*it);
    
    assert(s_it!=context.symbols.end());
    
    symbolt &symbol=s_it->second;
    
    function_name=symbol.base_name;
    
    const typet &return_type=
      static_cast<const typet &>(symbol.type.find(ID_return_type));

    number_of_returned_variables=vector_width(return_type);
    typecheck_code(to_code(symbol.value));
    symbol.value.type()=symbol.type;
  }
}

/*******************************************************************\

Function: bp_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bp_typecheck(
  bp_parse_treet &bp_parse_tree,
  contextt &context,
  const std::string &module,
  message_handlert &message_handler)
{
  bp_typecheckt bp_typecheck(
    bp_parse_tree,
    context,
    module,
    message_handler);

  return bp_typecheck.typecheck_main();
}
