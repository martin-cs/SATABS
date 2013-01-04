/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <context.h>

#include "program_formula.h"

/*******************************************************************\

Function: operator<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator<(const program_formulat::formula_goto_programt::const_targett i1,
               const program_formulat::formula_goto_programt::const_targett i2)
{
  const program_formulat::formula_goto_programt::instructiont &_i1=*i1;
  const program_formulat::formula_goto_programt::instructiont &_i2=*i2;
  return &_i1<&_i2;
}

/*******************************************************************\

Function: program_formulat::formula_goto_programt::output_other_instruction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream& program_formulat::formula_goto_programt::output_instruction(
  const namespacet &ns,
  const irep_idt &identifier,
  std::ostream &out,
  const_targett it) const
{
  assert(variables!=NULL);

  const instructiont instruction=*it;
  
  switch(instruction.type)
  {
  case RETURN:
    out << "return";

    if(!instruction.code.assigns.empty())
    {
      out << " ";
    
      for(program_formulat::assignst::const_iterator
          a_it=instruction.code.assigns.begin();
          a_it!=instruction.code.assigns.end();
          a_it++)
      {
        if(a_it!=instruction.code.assigns.begin())
          out << ",";

        a_it->value.output(out, *variables);
      }
    }
    
    out << ";" << std::endl;
    break;

  case ASSIGN:
    for(program_formulat::assignst::const_iterator
        it=instruction.code.assigns.begin();
        it!=instruction.code.assigns.end();
        it++)
    {
      if(it!=instruction.code.assigns.begin())
        out << ",";

      if(it->in_use)
        out << (*variables)[it->variable].display_name;
      else
        out << "_";
    }

    out << " = ";

    for(program_formulat::assignst::const_iterator
        a_it=instruction.code.assigns.begin();
        a_it!=instruction.code.assigns.end();
        a_it++)
    {
      if(a_it!=instruction.code.assigns.begin())
        out << ", ";

      a_it->value.output(out, *variables);
    }
    
    if(!instruction.code.constraint.is_true())
    {
      out << std::endl;
      out << "          CONSTRAINT: ";
      instruction.code.constraint.output(out, *variables);
    }
    
    out << std::endl;
    break;
  
  case FUNCTION_CALL:
    if(!instruction.code.function_lhs.empty())
    {
      for(program_formulat::formula_codet::function_lhst::const_iterator
          f_it=instruction.code.function_lhs.begin();
          f_it!=instruction.code.function_lhs.end();
          f_it++)
      {
        if(f_it!=instruction.code.function_lhs.begin())
          out << ",";

        if(f_it->in_use)
          out << (*variables)[f_it->variable].display_name;
        else
          out << "_";
      }

      out << " = ";
    }
    
    out << instruction.code.function << "(";

    for(program_formulat::formula_codet::function_argst::const_iterator
        f_it=instruction.code.function_args.begin();
        f_it!=instruction.code.function_args.end();
        f_it++)
    {
      if(f_it!=instruction.code.function_args.begin())
        out << ", ";

      f_it->output(out, *variables);
    }
    
    out << ")";
    
    if(!instruction.code.constraint.is_true())
    {
      out << std::endl;
      out << "          CONSTRAINT: ";
      instruction.code.constraint.output(out, *variables);
    }
    
    out << std::endl;
    break;

  case GOTO:
    if(!instruction.code.guard_expr.is_true())
    {
      out << "IF "
          << from_expr(ns, identifier, instruction.code.guard_expr)
          << " THEN ";
    }

    out << "GOTO ";
    
    for(instructiont::targetst::const_iterator
        gt_it=instruction.targets.begin();
        gt_it!=instruction.targets.end();
        gt_it++)
    {
      if(gt_it!=instruction.targets.begin()) out << ", ";
      out << (*gt_it)->target_number;
    }
      
    out << std::endl;
    break;
    
  case OTHER:
    out << "OTHER" << std::endl;
    break;
    
  case ASSUME:
  case ASSERT:
    if(instruction.is_assume())
      out << "ASSUME ";
    else
      out << "ASSERT ";
      
    {
      out << from_expr(ns, identifier, instruction.code.guard_expr);
    
      const irep_idt &comment=instruction.location.get("comment");
      if(comment!="") out << " // " << comment;
    }
      
    out << std::endl;
    break;
    
  case SKIP:
    out << "SKIP" << std::endl;
    break;
    
  case END_FUNCTION:
    out << "END_FUNCTION" << std::endl;
    break;
    
  case LOCATION:
    out << "LOCATION" << std::endl;
    break;
    
  case DEAD:
    out << "DEAD" << std::endl;
    break;
    
  case ATOMIC_BEGIN:
    out << "ATOMIC_BEGIN" << std::endl;
    break;
    
  case ATOMIC_END:
    out << "ATOMIC_END" << std::endl;
    break;
    
  case START_THREAD:
    out << "START THREAD ";

    if(instruction.targets.size()==1)
      out << instruction.targets.front()->target_number;
    
    out << std::endl;
    break;
    
  case END_THREAD:
    out << "END THREAD" << std::endl;
    break;
    
  case DECL:
    out << "DECL" << std::endl;
    break;
    
  case THROW:
    out << "THROW" << std::endl;
    break;
  
  case CATCH:
    out << "CATCH" << std::endl;
    break;
  
  default: out << "UNKNOWN" << std::endl;
  }

  return out;
}

/*******************************************************************\

Function: program_formulat::show_alive

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void program_formulat::show_alive(std::ostream &out) const
{
  for(function_mapt::const_iterator
      f_it=function_map.begin();
      f_it!=function_map.end();
      f_it++)
  {
    const formula_goto_programt &program=f_it->second.body;
  
    for(formula_goto_programt::instructionst::const_iterator
        i_it=program.instructions.begin();
        i_it!=program.instructions.end();
        i_it++)
    {
      out << i_it->location << std::endl;
      for(std::set<unsigned>::const_iterator
          v_it=i_it->code.alive.begin();
          v_it!=i_it->code.alive.end();
          v_it++)
        out << " " << variables[*v_it].display_name;
      out << std::endl;
    }
  }
}

/*******************************************************************\

Function: program_formulat::show_cycles

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void program_formulat::show_cycles(
  const namespacet &ns,
  std::ostream &out) const
{
  for(function_mapt::const_iterator
      f_it=function_map.begin();
      f_it!=function_map.end();
      f_it++)
  {
    const formula_goto_programt &program=f_it->second.body;
  
    for(formula_goto_programt::instructionst::const_iterator
        it=program.instructions.begin();
        it!=program.instructions.end();
        it++)
      if(it->code.can_form_cycle)
      {
        program.output_instruction(ns, "", out, it);

        out << std::endl;
      }
  }
}

/*******************************************************************\

Function: program_formulat::formula_goto_programt::find_cycles

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void program_formulat::formula_goto_programt::find_cycles()
{
  compute_incoming_edges();

  for(instructionst::iterator it=instructions.begin();
      it!=instructions.end();
      it++)
    it->code.can_form_cycle=false;

  if(!instructions.front().incoming_edges.empty())
    instructions.front().code.can_form_cycle=true;

  for(instructionst::iterator it=instructions.begin();
      it!=instructions.end();
      it++)
  {
    if(it->incoming_edges.size()>=2)
      it->code.can_form_cycle=true;
  }
}

/*******************************************************************\

Function: operator<<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream& operator<< (
  std::ostream &out,
  const program_formulat::formula_goto_programt &program)
{
  contextt context;
  namespacet ns(context);
  return program.output(ns, "", out);
}

/*******************************************************************\

Function: operator<<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream& operator<< (
  std::ostream &out,
  const program_formulat::variablest &variables)
{
  for(program_formulat::variablest::const_iterator
      v_it=variables.begin();
      v_it!=variables.end();
      v_it++)
  {
    out << v_it->identifier << std::endl;
  }
  
  return out;
}

/*******************************************************************\

Function: program_formulat::compute_alive

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void program_formulat::compute_alive()
{
  for(function_mapt::iterator
      f_it=function_map.begin();
      f_it!=function_map.end();
      f_it++)
  {
    formula_goto_programt &program=f_it->second.body;
  
    for(formula_goto_programt::instructionst::iterator
        it=program.instructions.begin();
        it!=program.instructions.end();
        it++)
    {
      // for now, just take all variables
      for(unsigned v=0; v<variables.size(); v++)
      {
        //if(variables[v].is_global)
        it->code.alive.insert(v);
      }
    }
  }
}

/*******************************************************************\

Function: program_formulat::find_cycles

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void program_formulat::find_cycles()
{
  for(function_mapt::iterator
      f_it=function_map.begin();
      f_it!=function_map.end();
      f_it++)
  {
    formula_goto_programt &program=f_it->second.body;
  
    program.find_cycles();
  }
}

