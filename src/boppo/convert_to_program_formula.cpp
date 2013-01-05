/*******************************************************************\

Module: Conversion to Program Formula

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#include <assert.h>

#include <expr_util.h>
#include <cout_message.h>
#include <std_code.h>
#include <std_expr.h>

#include <bplang/bp_util.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_check.h>
#include <goto-programs/goto_convert_functions.h>

#include "convert_to_program_formula.h"

class convert_to_program_formulat
{
public:
  convert_to_program_formulat(
    contextt &_context,
    program_formulat &_program_formula,
    formula_containert &_formula_container,
    const std::string &_error_label):
    context(_context),
    program_formula(_program_formula),
    formula_container(_formula_container),
    error_label(_error_label)
  {
  }

  void convert_main_code(bool inlining);
  void convert_global_variables();
  void convert_local_variables(const goto_programt &goto_program);

protected:
  contextt &context;
  program_formulat &program_formula;
  formula_containert &formula_container;
  const std::string &error_label;
  
  typedef program_formulat::formula_goto_programt formula_goto_programt;
  
  void convert_decl(
    formula_goto_programt::instructiont &instr);

  void convert_return(
    formula_goto_programt::instructiont &instr);

  void convert_assign(
    formula_goto_programt::instructiont &instr,
    const codet &code,
    const exprt &constraint);

  void convert_constrain(
    formula_goto_programt::instructiont &instr);

  void convert_functioncall(
    formula_goto_programt::instructiont &instr,
    const exprt &lhs,
    const exprt &function,
    const exprt::operandst &arguments,
    const exprt &constraint);

  formulat convert_expr(const exprt &expr);

  unsigned convert_variable(const exprt &expr);
  unsigned convert_variable(const irep_idt &id);

  void convert_goto_program(
    const goto_programt &goto_program,
    formula_goto_programt &formula_goto_program);

  void convert_other(
    formula_goto_programt::instructiont &instr);

  bool is_symbol(const exprt &expr) const
  {
    return expr.id()==ID_symbol ||
           expr.id()=="temp_symbol" ||
           expr.id()==ID_next_symbol;
  }
};

/*******************************************************************\

Function: convert_to_program_formulat::convert_global_variables

  Inputs:

 Outputs:

 Purpose: convert global variables

\*******************************************************************/

void convert_to_program_formulat::convert_global_variables()
{
  const namespacet ns(context);
  
  program_formula.no_globals=0;

  forall_symbols(it, context.symbols)
  {
    const symbolt &symbol=it->second;

    if(symbol.is_static_lifetime &&
       symbol.is_lvalue &&
       symbol.is_state_var)
    {
      unsigned nr=program_formula.variables.size();

      program_formula.no_globals++;

      program_formula.variables.push_back(program_formulat::variablet());
      
      program_formulat::variablet &variable=
        program_formula.variables.back();

      variable.identifier=symbol.name;
      variable.base_name=symbol.base_name;
      variable.display_name=symbol.display_name();
      variable.is_global=true;
      
      program_formula.variable_map[symbol.name]=nr;
      
      assert(symbol.type.id()==ID_bool);
    }
  }  
}

/*******************************************************************\

Function: convert_to_program_formulat::convert_local_variables

  Inputs:

 Outputs:

 Purpose: convert global variables

\*******************************************************************/

void convert_to_program_formulat::convert_local_variables(
  const goto_programt &goto_program)
{
  forall_symbols(it, context.symbols)
  {
    const symbolt &symbol=it->second;

    if(!symbol.is_static_lifetime &&
       symbol.is_lvalue &&
       symbol.is_state_var)
    {
      assert(symbol.type.id()==ID_bool);

      unsigned nr=program_formula.variables.size();

      program_formula.variables.push_back(program_formulat::variablet());
    
      program_formulat::variablet &variable=
        program_formula.variables.back();

      variable.identifier=symbol.name;
      variable.base_name=symbol.base_name;
      variable.is_global=false;
      variable.display_name=symbol.display_name();
    
      program_formula.variable_map[symbol.name]=nr;

      program_formula.no_locals++;  
    }
  }  
}

/*******************************************************************\

Function: convert_to_program_formulat::convert_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

formulat convert_to_program_formulat::convert_expr(const exprt &expr)
{
  formulat result=formulat(NULL);

  if(expr.id()==ID_symbol ||
     expr.id()==ID_next_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);

    const program_formulat::variable_mapt::const_iterator v_it=
      program_formula.variable_map.find(identifier);

    if(v_it==program_formula.variable_map.end())
    {
      std::cerr << "failed to find symbol " << identifier
                << " in variable map" << std::endl;
      assert(false);
    }
    
    formula_nodet::idt id=
      expr.id()==ID_symbol?formula_nodet::VARIABLE
                          :formula_nodet::NEXT_VARIABLE;
    
    result=formula_container.new_node(id, v_it->second);
  }
  else if(expr.id()==ID_constant)
  {
    if(expr.is_true())
      result=formula_container.gen_true();
    else if(expr.is_false())
      result=formula_container.gen_false();
    else
      assert(false);
  }
  else if(expr.id()==ID_and ||
          expr.id()==ID_or)
  {
    assert(expr.operands().size()!=0);
    
    formula_nodet::idt id=
      expr.id()==ID_and?formula_nodet::AND:formula_nodet::OR;

    result=convert_expr(expr.op0());
    
    for(unsigned i=1; i<expr.operands().size(); i++)
      result=formula_container.new_node(id, result,
        convert_expr(expr.operands()[i]));
  }
  else if(expr.id()==ID_xor || expr.id()==ID_notequal)
  {
    assert(expr.operands().size()==2);
    
    result=formula_container.new_node(
      formula_nodet::XOR,
      convert_expr(expr.op0()),
      convert_expr(expr.op1()));
  }
  else if(expr.id()==ID_equal)
  {
    assert(expr.operands().size()==2);
    
    result=formula_container.new_node(
      formula_nodet::IFF,
      convert_expr(expr.op0()),
      convert_expr(expr.op1()));
  }
  else if(expr.id()==ID_not)
  {
    assert(expr.operands().size()==1);

    result=formula_container.gen_not(convert_expr(expr.op0()));
  }
  else if(expr.id()==ID_nondet_bool)
  {
    result=formula_container.gen_nondet();
  }
  else if(expr.id()==ID_sideeffect)
  {
    const irep_idt &statement=expr.get(ID_statement);
    
    if(statement==ID_nondet)
    {
      result=formula_container.gen_nondet();
    }
    else
    {
      std::cerr << "unexpected sideeffect: "
                << expr.pretty() << std::endl;
      assert(false);
    }
  }
  else
  {
    std::cerr << "unexpected expression: "
              << expr.pretty() << std::endl;
    assert(false);
  }
  
  return result;
}

/*******************************************************************\

Function: convert_to_program_formulat::convert_variable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned convert_to_program_formulat::convert_variable(const exprt &expr)
{
  if(expr.id()!=ID_symbol)
    throw "expected variable";

  const irep_idt &identifier=expr.get(ID_identifier);
  
  return convert_variable(identifier);
}

/*******************************************************************\

Function: convert_to_program_formulat::convert_variable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned convert_to_program_formulat::convert_variable(
  const irep_idt &identifier)
{
  const program_formulat::variable_mapt::const_iterator v_it=
    program_formula.variable_map.find(identifier);

  if(v_it==program_formula.variable_map.end())
  {
    std::cerr << "failed to find symbol " << identifier
              << " in variable map" << std::endl;
    assert(false);
  }
  
  return v_it->second;
}

/*******************************************************************\

Function: convert_to_program_formulat::convert_main_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_program_formulat::convert_main_code(bool inlining)
{
  goto_functionst goto_functions;
  console_message_handlert message_handler;

  goto_convert(context, goto_functions, message_handler);

  // we do want the assertions
  optionst options;
  options.set_option("assertions", true);
  options.set_option("error-label", error_label);
  
  const namespacet ns(context);
  goto_check(ns, options, goto_functions);

  program_formula.no_locals=0;

  if(inlining)
  {
    const contextt context;
    goto_inline(goto_functions, ns, message_handler);

    goto_programt &goto_program=goto_functions.function_map["main"].body;

    convert_local_variables(goto_program);

    formula_goto_programt &program=program_formula.function_map["main"].body;

    program.variables=&program_formula.variables;
    convert_goto_program(goto_program, program);
    program.compute_location_numbers();
  }
  else
  {
    for(goto_functionst::function_mapt::const_iterator
        f_it=goto_functions.function_map.begin();
        f_it!=goto_functions.function_map.end();
        f_it++)
    {
      convert_local_variables(f_it->second.body);

      program_formulat::functiont &f=program_formula.function_map[f_it->first];
      
      // args
      const code_typet::argumentst &arguments=
        f_it->second.type.arguments();
      
      f.args.resize(arguments.size());

      for(unsigned i=0; i<f.args.size(); i++)
        f.args[i]=convert_variable(arguments[i].get_identifier());
      
      // return value
      const typet &return_type=f_it->second.type.return_type();

      if(return_type.id()==ID_empty)
        f.number_of_return_values=0;
      else if(return_type.id()==ID_bool)
        f.number_of_return_values=1;
      else if(return_type.id()=="bool-vector")
        f.number_of_return_values=return_type.get_int(ID_width);
      else
        assert(false);
      
      // body
      formula_goto_programt &program=f.body;

      program.variables=&program_formula.variables;
      convert_goto_program(f_it->second.body, program);
    }

    goto_functions.compute_location_numbers();
  }
}

/*******************************************************************\

Function: convert_to_program_formulat::convert_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_program_formulat::convert_goto_program(
  const goto_programt &goto_program,
  program_formulat::formula_goto_programt &formula_goto_program)
{
  // Definitions for mapping between the two programs
  typedef std::map<goto_programt::const_targett,
                   program_formulat::formula_goto_programt::targett> targets_mappingt;

  targets_mappingt targets_mapping;

  // Loop over program - 1st time collects targets

  forall_goto_program_instructions(it, goto_program)
  {
    program_formulat::formula_goto_programt::instructionst::iterator
      new_formula_instruction=
      formula_goto_program.add_instruction();

    targets_mapping[it]=new_formula_instruction;

    // copy location
    new_formula_instruction->location=it->location;

    // copy type
    new_formula_instruction->type=it->type;

    // copy labels
    new_formula_instruction->labels=it->labels;

    // copy guard
    new_formula_instruction->code.guard_expr=it->guard;

    // copy code
    new_formula_instruction->code.code_expr=it->code;
  }

  // Loop over program - 2nd time updates goto targets
  forall_goto_program_instructions(it, goto_program)
  {
    if(it->is_goto() || it->is_start_thread())
    {
      targets_mappingt::iterator formula_it=targets_mapping.find(it);

      if(formula_it==targets_mapping.end())
        throw "formula instruction not found";

      for(goto_programt::instructiont::targetst::const_iterator
          t_it=it->targets.begin();
          t_it!=it->targets.end();
          t_it++)
      {
        targets_mappingt::iterator
          formula_target_it=targets_mapping.find(*t_it);

        if(formula_target_it==targets_mapping.end())
          throw "goto target not found";

        formula_it->second->targets.push_back(formula_target_it->second);
      }
    }
  }
  
  formula_goto_program.update();

  // compute new stuff

  for(program_formulat::formula_goto_programt::instructionst::iterator
      it=formula_goto_program.instructions.begin();
      it!=formula_goto_program.instructions.end();
      it++)
  {
    if(it->is_goto() ||
       it->is_assert() ||
       it->is_assume())
    {
      // if its a goto/assume/assert, convert the guard
      it->guard=convert_expr(it->code.guard_expr);
    }
    else if(it->is_dead())
    {
    }
    else if(it->is_return())
      convert_return(*it);
    else if(it->is_assign())
      convert_assign(*it, to_code(it->code.code_expr), true_exprt());
    else if(it->is_function_call())
    {
      const code_function_callt &code=
        to_code_function_call(to_code(it->code.code_expr));

      convert_functioncall(
        *it,
        code.lhs(),
        code.function(),
        code.arguments(),
        true_exprt());
    }
    else if(it->is_other())
      convert_other(*it);
  }
  
  // analyze variable liveness
  program_formula.compute_alive();
}

/*******************************************************************\

Function: convert_to_program_formulat::convert_other

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_program_formulat::convert_other(
  program_formulat::formula_goto_programt::instructiont &instr)
{
  const exprt &code=instr.code.code_expr;

  instr.type=SKIP;
  
  if(code.is_nil())
    return;

  assert(code.id()==ID_code);

  const irep_idt &statement=code.get(ID_statement);

  if(statement==ID_decl)
  {
    convert_decl(instr);
  }
  else if(statement==ID_assign)
    assert(false);
  else if(statement=="bp_constrain")
  {
    convert_constrain(instr);
  }
  else if(statement=="bp_enforce")
  {
    assert(code.operands().size()==1);
    assert(false); // should not be here
  }
  else if(statement=="bp_dead")
  {
    // do nothing for now
  }
  else if(statement==ID_skip || statement==ID_expression)
  {
    // do nothing
  }
  else if(statement==ID_function_call)
    assert(false);
  else
  {
    std::cerr << "convert_to_program_formulat: unexpected statement: "
              << statement << ": " << code << std::endl;
    assert(false);
  }
}

/*******************************************************************\

Function: convert_to_program_formulat::convert_return

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_program_formulat::convert_return(
  program_formulat::formula_goto_programt::instructiont &instr)
{
  const exprt &code=instr.code.code_expr;
  
  if(code.operands().size()==1)
  {
    const exprt &return_value=code.op0();
    
    if(return_value.id()=="bool-vector")
    {
      instr.code.assigns.resize(return_value.operands().size());
      
      for(unsigned i=0; i<instr.code.assigns.size(); i++)
        instr.code.assigns[i].value=convert_expr(return_value.operands()[i]);
    }
    else
    {
      instr.code.assigns.resize(1);
      instr.code.assigns[0].value=convert_expr(return_value);
    }
  }
}

/*******************************************************************\

Function: convert_to_program_formulat::convert_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_program_formulat::convert_assign(
  program_formulat::formula_goto_programt::instructiont &instr,
  const codet &code,
  const exprt &constraint)
{
  assert(code.operands().size()==2);

  const exprt &lhs=code.op0();
  const exprt &rhs=code.op1();
  
  // convert constraint
  instr.code.constraint=convert_expr(constraint);

  exprt final_lhs(lhs), final_rhs(rhs);
  
  unsigned nr;
  
  if(final_lhs.id()=="bool-vector")
  {
    assert(final_rhs.id()=="bool-vector");
    nr=final_lhs.operands().size();
  }
  else
  {
    // make it into a vector of size one
    exprt tmp_lhs, tmp_rhs;
    tmp_lhs.move_to_operands(final_lhs);
    tmp_rhs.move_to_operands(final_rhs);
    final_lhs.swap(tmp_lhs);
    final_rhs.swap(tmp_rhs);
    nr=1;
  }

  assert(nr==final_rhs.operands().size());
  
  for(unsigned i=0; i<nr; i++)
  {
    instr.code.assigns.push_back(program_formulat::assignt());
    program_formulat::assignt &assign=instr.code.assigns.back();

    if(final_lhs.operands()[i].id()=="bp_unused")
      assign.in_use=false;
    else
    {
      assign.in_use=true;
      assign.variable=convert_variable(final_lhs.operands()[i]);
      assign.value=convert_expr(final_rhs.operands()[i]);
    }
  }
}

/*******************************************************************\

Function: convert_to_program_formulat::convert_functioncall

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_program_formulat::convert_functioncall(
  program_formulat::formula_goto_programt::instructiont &instr,
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  const exprt &constraint)
{
  instr.code.constraint=convert_expr(constraint);

  if(function.id()!=ID_symbol)
    throw "function_call expects symbol as function";
  
  instr.code.function=function.get(ID_identifier);
  
  instr.code.function_args.resize(arguments.size());
  
  for(unsigned i=0; i<instr.code.function_args.size(); i++)
    instr.code.function_args[i]=convert_expr(arguments[i]);

  if(lhs.is_nil())
  {
    instr.code.function_lhs.clear();
  }
  else if(lhs.id()=="bool-vector")
  {
    instr.code.function_lhs.resize(lhs.operands().size());

    for(unsigned i=0; i<instr.code.function_lhs.size(); i++)
    {
      if(lhs.operands()[i].id()=="bp_unused")
        instr.code.function_lhs[i].in_use=false;
      else
      {
        instr.code.function_lhs[i].in_use=true;
        instr.code.function_lhs[i].variable=convert_variable(lhs.operands()[i]);
      }
    }
  }
  else
  {
    instr.code.function_lhs.resize(1);
    
    if(lhs.id()=="bp_unused")
      instr.code.function_lhs[0].in_use=false;
    else
    {
      instr.code.function_lhs[0].in_use=true;
      instr.code.function_lhs[0].variable=convert_variable(lhs);
    }
  }
}

/*******************************************************************\

Function: convert_to_program_formulat::convert_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_program_formulat::convert_decl(
  program_formulat::formula_goto_programt::instructiont &instr)
{
  codet &code=to_code(instr.code.code_expr);

  assert(code.operands().size()==1); // we don't do initialization
  
  const exprt &op=code.op0();
  assert(op.id()==ID_symbol);

  instr.type=ASSIGN;

  // convert constraint
  instr.code.constraint=formula_container.gen_true();

  instr.code.assigns.push_back(program_formulat::assignt());
  program_formulat::assignt &assign=instr.code.assigns.back();

  assign.variable=convert_variable(op);
  assign.value=formula_container.gen_nondet();
  assign.in_use=true;
}

/*******************************************************************\

Function: convert_to_program_formulat::convert_constrain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_program_formulat::convert_constrain(
  program_formulat::formula_goto_programt::instructiont &instr)
{
  assert(instr.code.code_expr.operands().size()==2);
  
  const codet &other_code=to_code(instr.code.code_expr.op0());
  const exprt &constraint=instr.code.code_expr.op1();

  const irep_idt &statement=other_code.get_statement();
  
  if(statement==ID_assign)
  {
    instr.type=ASSIGN;
    convert_assign(instr, other_code, constraint);
  }
  else if(statement==ID_function_call)
  {
    instr.type=FUNCTION_CALL;

    convert_functioncall(
      instr, other_code.op0(),
      other_code.op1(),
      other_code.op2().operands(),
      constraint);
  }
  else
    assert(false);
}

/*******************************************************************\

Function: convert_to_program_formula

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_program_formula(
  contextt &context,
  program_formulat &program_formula,
  formula_containert &formula_container,
  const std::string &error_label,
  bool inlining)
{
  convert_to_program_formulat convert_to_program_formula(
    context, program_formula, formula_container, error_label);
  
  convert_to_program_formula.convert_global_variables();

  convert_to_program_formula.convert_main_code(inlining);

  program_formula.find_cycles();
}
