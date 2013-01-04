/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include "formula.h"
#include "program_formula.h"

formula_nodet formula_nodet::true_node(formula_nodet::CONST_TRUE);
formula_nodet formula_nodet::false_node(formula_nodet::CONST_FALSE);

/*******************************************************************\

Function: formulat::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void formulat::output(
  std::ostream &out,
  const variablest &variables) const
{
  switch(id())
  {
  case formula_nodet::NONE:
    out << "NONE";
    break;
    
  case formula_nodet::VARIABLE:
    assert(node->variable<variables.size());
    out << variables[node->variable].display_name;
    break;
    
  case formula_nodet::NEXT_VARIABLE:
    out << "'" << variables[node->variable].display_name;
    break;
    
  case formula_nodet::NONDET:
    out << "*";
    if(node->l_is_set) out << ":" << node->l.dimacs();
    break;
    
  case formula_nodet::CONST_TRUE:
    out << "T";
    break;
    
  case formula_nodet::CONST_FALSE:
    out << "F";
    break;
    
  case formula_nodet::AND:
    output_op(out, a(), variables);
    out << " & ";
    output_op(out, b(), variables);
    break;
    
  case formula_nodet::NOT:
    out << "!";
    output_op(out, a(), variables);
    break;
    
  case formula_nodet::OR:
    output_op(out, a(), variables);
    out << " | ";
    output_op(out, b(), variables);
    break;
    
  case formula_nodet::IFF:
    output_op(out, a(), variables);
    out << " <-> ";
    output_op(out, b(), variables);
    break;
    
  case formula_nodet::XOR:
    output_op(out, a(), variables);
    out << " ^ ";
    output_op(out, b(), variables);
    break;
    
  default: assert(false);
  }
}

/*******************************************************************\

Function: formulat::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void formulat::output(std::ostream &out) const
{
  switch(node->id)
  {
  case formula_nodet::NONE:
    out << "NONE";
    break;
    
  case formula_nodet::VARIABLE:
    out << "v" << node->variable;
    break;
    
  case formula_nodet::NEXT_VARIABLE:
    out << "'v" << node->variable;
    break;
    
  case formula_nodet::NONDET:
    out << "*";
    if(node->l_is_set) out << ":" << node->l.dimacs();
    break;
    
  case formula_nodet::CONST_TRUE:
    out << "T";
    break;
    
  case formula_nodet::CONST_FALSE:
    out << "F";
    break;
    
  case formula_nodet::AND:
    output_op(out, a());
    out << " & ";
    output_op(out, b());
    break;
    
  case formula_nodet::NOT:
    out << "!";
    output_op(out, a());
    break;
    
  case formula_nodet::OR:
    output_op(out, a());
    out << " | ";
    output_op(out, b());
    break;
    
  case formula_nodet::IFF:
    output_op(out, a());
    out << " <-> ";
    output_op(out, b());
    break;
    
  case formula_nodet::XOR:
    output_op(out, a());
    out << " ^ ";
    output_op(out, b());
    break;
    
  default: assert(false);
  }
}

/*******************************************************************\

Function: formulat::output_op

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void formulat::output_op(
  std::ostream &out,
  const formulat op,
  const variablest &variables) const
{
  bool parens=op.node->id!=node->id &&
       op.id()!=formula_nodet::VARIABLE &&
       op.id()!=formula_nodet::NEXT_VARIABLE &&
       op.id()!=formula_nodet::CONST_TRUE &&
       op.id()!=formula_nodet::CONST_FALSE &&
       op.id()!=formula_nodet::NONDET;
  
  if(parens) out << "(";
  
  op.output(out, variables);
  
  if(parens) out << ")";
}

/*******************************************************************\

Function: formulat::output_op

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void formulat::output_op(
  std::ostream &out,
  const formulat op) const
{
  bool parens=op.id()!=id() &&
       op.id()!=formula_nodet::VARIABLE &&
       op.id()!=formula_nodet::NEXT_VARIABLE &&
       op.id()!=formula_nodet::CONST_TRUE &&
       op.id()!=formula_nodet::CONST_FALSE &&
       op.id()!=formula_nodet::NONDET;
  
  if(parens) out << "(";
  
  op.output(out);
  
  if(parens) out << ")";
}

/*******************************************************************\

Function: formulat::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt formulat::convert(propt &prop) const
{
  if(node->l_is_set)
    return node->l;
    
  switch(id())
  {
  case formula_nodet::CONST_TRUE:
    node->l=const_literal(true);
    break;
    
  case formula_nodet::CONST_FALSE:
    node->l=const_literal(false);
    break;

  case formula_nodet::VARIABLE:
  case formula_nodet::NEXT_VARIABLE:
    assert(false);
    break;
    
  case formula_nodet::NONDET:
    node->l=prop.new_variable();
    break;

  case formula_nodet::NOT:
    node->l=prop.lnot(a().convert(prop));
    break;

  case formula_nodet::AND:
    node->l=prop.land(a().convert(prop), b().convert(prop));
    break;

  case formula_nodet::OR:
    node->l=prop.lor(a().convert(prop), b().convert(prop));
    break;

  case formula_nodet::IFF:
    node->l=prop.lequal(a().convert(prop), b().convert(prop));
    break;

  case formula_nodet::XOR:
    node->l=prop.lxor(a().convert(prop), b().convert(prop));
    break;

  default:
    assert(false);
  }
  
  node->l_is_set=true;
  
  return node->l;
}

/*******************************************************************\

Function: formulat::get_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void formulat::get_variables(
  std::set<unsigned> &variables) const
{
  switch(id())
  {
  case formula_nodet::CONST_TRUE:
  case formula_nodet::CONST_FALSE:
    break;

  case formula_nodet::VARIABLE:
    variables.insert(node->variable);
    break;

  case formula_nodet::NEXT_VARIABLE:
    break;
    
  case formula_nodet::NONDET:
    break;

  case formula_nodet::NOT:
    a().get_variables(variables);
    break;

  case formula_nodet::AND:
  case formula_nodet::OR:
  case formula_nodet::IFF:
  case formula_nodet::XOR:
    a().get_variables(variables);
    b().get_variables(variables);
    break;

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: formulat::get_global_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void formulat::get_global_variables(
  std::set<unsigned> &variable_set,
  const variablest &variables) const
{
  switch(id())
  {
  case formula_nodet::CONST_TRUE:
  case formula_nodet::CONST_FALSE:
    break;

  case formula_nodet::VARIABLE:
    if(!variables[node->variable].is_global)
      break;

    variable_set.insert(node->variable);
    break;

  case formula_nodet::NEXT_VARIABLE:
    break;
    
  case formula_nodet::NONDET:
    break;

  case formula_nodet::NOT:
    a().get_global_variables(variable_set, variables);
    break;

  case formula_nodet::AND:
  case formula_nodet::OR:
  case formula_nodet::IFF:
  case formula_nodet::XOR:
    a().get_global_variables(variable_set, variables);
    b().get_global_variables(variable_set, variables);
    break;

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: formulat::get_nondet_literals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void formulat::get_nondet_literals(std::set<literalt> &literals) const
{
  switch(id())
  {
  case formula_nodet::CONST_TRUE:
  case formula_nodet::CONST_FALSE:
  case formula_nodet::VARIABLE:
  case formula_nodet::NEXT_VARIABLE:
    break;
    
  case formula_nodet::NONDET:
    assert(node->l_is_set);
    literals.insert(node->l);
    break;

  case formula_nodet::NOT:
    a().get_nondet_literals(literals);
    break;

  case formula_nodet::AND:
  case formula_nodet::OR:
  case formula_nodet::IFF:
  case formula_nodet::XOR:
    a().get_nondet_literals(literals);
    b().get_nondet_literals(literals);
    break;

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: formula_containert::gen_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

formulat formula_containert::gen_if(
  formulat cond, formulat a, formulat b)
{
  if(cond.is_true()) return a;
  if(cond.is_false()) return b;
  if(a==b) return a;
  
  formulat cond_and_a=gen_and(cond, a);
  formulat not_cond=gen_not(cond);
  formulat not_cond_and_b=gen_and(not_cond, b);

  return gen_or(cond_and_a, not_cond_and_b);
}

/*******************************************************************\

Function: formula_containert::gen_and

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

formulat formula_containert::gen_and(formulat a, formulat b)
{
  // propagate constants
  if(a.is_true()) return b;  // T & b
  if(b.is_true()) return a;  // a & T
  if(a.is_false()) return a; // F & b
  if(b.is_false()) return b; // a & F

  return new_node(formula_nodet::AND, a, b);
}

/*******************************************************************\

Function: formula_containert::gen_or

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

formulat formula_containert::gen_or(formulat a, formulat b)
{
  // propagate constants
  if(a.is_true()) return a;  // T | b
  if(b.is_true()) return b;  // a | T
  if(a.is_false()) return b; // F | b
  if(b.is_false()) return a; // a | F

  return new_node(formula_nodet::OR, a, b);
}

/*******************************************************************\

Function: formula_containert::gen_not

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

formulat formula_containert::gen_not(formulat a)
{
  // propagate constants
  if(a.is_true()) return gen_false();
  if(a.is_false()) return gen_true();
  
  return new_node(formula_nodet::NOT, a);
}

/*******************************************************************\

Function: formula_containert::duplicate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

formulat formula_containert::duplicate(formulat formula)
{
  if(formula.node==NULL) return formula;

  return new_node(formula.id(),
                  duplicate(formula.a()),
                  duplicate(formula.b()));
}

/*******************************************************************\

Function: formula_containert::reset_prop

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void formula_containert::reset_prop()
{
  for(node_listt::iterator it=node_list.begin();
      it!=node_list.end();
      it++)
    it->l_is_set=false;
}

/*******************************************************************\

Function: formula_containert::get_nondet_literals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void formula_containert::get_nondet_literals(std::set<literalt> &literals) const
{
  for(node_listt::const_iterator it=node_list.begin();
      it!=node_list.end();
      it++)
    if(it->l_is_set && it->id==formula_nodet::NONDET)
      literals.insert(it->l);
}

