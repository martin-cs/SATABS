/*******************************************************************\

Module: Conversion to PROMELA

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#include <assert.h>

#include <i2string.h>
#include <std_expr.h>
#include <prefix.h>

#include <bplang/bp_util.h>

#include "convert_to_promela.h"

class convert_to_promelat
{
public:
  convert_to_promelat(const contextt &_context,
                      std::ostream &_out):
    context(_context), out(_out),
    temp_symbol_counter(0)
  {
  }

  void convert();

protected:
  const contextt &context;
  std::ostream &out;
  
  void convert_global_variables();
  void find_threads_rec(const exprt &code);
  void find_threads(const exprt &code);
  void convert_functions();
  void convert_function(const symbolt &symbol);
  void convert_code(const exprt &code, unsigned indent);
  void convert_ifthenelse(const exprt &code, unsigned indent);
  void convert_assign(const exprt &code, unsigned indent,
                      const exprt &constraint);
  void convert_decl(const exprt &code, unsigned indent);
  void convert_assume(const exprt &code, unsigned indent);
  void convert_constrain(const exprt &code, unsigned indent);
  void convert_assert(const exprt &code, unsigned indent);
  void convert_return(const exprt &code, unsigned indent);
  void convert_label(const exprt &code, unsigned indent);
  void convert_functioncall(const exprt &code, unsigned indent,
                            const exprt &lhs);
  void convert_non_deterministic_goto(const exprt &code, unsigned indent);
  void convert_expr(const exprt &expr);
  void do_indent(unsigned indent);
  void remove_non_determinism(exprt &expr, unsigned indent);

  unsigned temp_symbol_counter;
  
  typedef std::vector<irep_idt> threadst;
  threadst threads;

  unsigned number_of_returned_variables;
  bool is_main;
  
  typedef std::map<irep_idt, irep_idt> next_symbol_mappingt;
  next_symbol_mappingt next_symbol_mapping;
  
  bool is_symbol(const exprt &expr) const
  {
    return expr.id()=="symbol" || expr.id()=="temp_symbol" ||
           expr.id()=="next_symbol";
  }
};

/*******************************************************************\

Function: convert_to_promelat::convert_global_variables

  Inputs:

 Outputs:

 Purpose: convert global variables

\*******************************************************************/

void convert_to_promelat::convert_global_variables()
{
  out << std::endl;
  out << "/* Global Variables */" << std::endl;
  out << std::endl;

  forall_symbols(it, context.symbols)
  {
    const symbolt &symbol=it->second;

    if(symbol.is_static_lifetime &&
       symbol.is_lvalue &&
       symbol.is_state_var)
      out << "bool var_" << symbol.base_name << ";" << std::endl;
  }  
  
  out << std::endl;
}

/*******************************************************************\

Function: convert_to_promelat::convert_functions

  Inputs:

 Outputs:

 Purpose: convert functions

\*******************************************************************/

void convert_to_promelat::convert_functions()
{
  out << "/* Functions */" << std::endl;
  out << std::endl;

  forall_symbols(it, context.symbols)
  {
    const symbolt &symbol=it->second;

    if(!symbol.is_state_var && symbol.type.id()=="code")
      convert_function(symbol);
  }
}

/*******************************************************************\

Function: convert_to_promelat::convert_function

  Inputs:

 Outputs:

 Purpose: convert functions

\*******************************************************************/

void convert_to_promelat::convert_function(const symbolt &symbol)
{
  out << "/* Function " << symbol.base_name << " */" << std::endl;

  is_main=symbol.base_name=="main";
  
  if(is_main)
  {
    find_threads(symbol.value);

    out << "proctype fkt_" << symbol.base_name;
  
    out << "(byte thread_id)" << std::endl;
  
    out << "{" << std::endl;
    
    do_indent(1);
    out << "/* thread selector */" << std::endl;

    do_indent(1);
    out << "if" << std::endl;
    
    do_indent(1);
    out << ":: thread_id == MAIN -> skip;" << std::endl;

    for(threadst::const_iterator it=threads.begin();
        it!=threads.end(); it++)
    {
      do_indent(1);
      out << ":: thread_id == THREAD_" << *it
          << " -> goto LABEL_"
          << *it << ";" << std::endl;
    }
    
    do_indent(1);
    out << "fi;" << std::endl << std::endl;
  }
  else
  {
    out << "proctype fkt_" << symbol.base_name;
  
    out << "(";
    out << "chan return_value";
    
    const irept &argument_types=symbol.type.find("argument_types");
    
    forall_irep(it, argument_types.get_sub())
      out << "; bool var_" << it->get("#base_name");
    
    out << ")" << std::endl;

    out << "{" << std::endl;
  }

  const typet &return_type=(typet &)symbol.type.find("return_type");

  number_of_returned_variables=vector_width(return_type);
  
  convert_code(symbol.value, 1);
  
  do_indent(1);
  out << "return_target: skip;" << std::endl;

  out << "} /* end of function " << symbol.base_name
      << " */" << std::endl;
  out << std::endl;  
}

/*******************************************************************\

Function: convert_to_promelat::find_threads_rec

  Inputs:

 Outputs:

 Purpose: produce #define's for threads

\*******************************************************************/

void convert_to_promelat::find_threads_rec(const exprt &code)
{
  assert(code.id()=="code");

  const irep_idt &statement=code.get("statement");
  
  if(statement=="label")
  {
    const irep_idt &label=code.get("label");

    if(has_prefix(id2string(label), "ASYNC_"))
      threads.push_back(label); // found thread

    assert(code.operands().size()==1);
    
    find_threads_rec(code.op0());
  }
  else if(statement=="bp_start_thread")
  {
    assert(code.operands().size()==1);
    
    find_threads_rec(code.op0());
  }
  else if(statement=="ifthenelse")
  {
    if(code.operands().size()==2)
      find_threads_rec(code.op1());
    else if(code.operands().size()==3)
    {
      find_threads_rec(code.op1());
      find_threads_rec(code.operands()[2]);
    }
    else
      assert(false);
  }
  else if(statement=="block")
  {
    forall_operands(it, code)
      find_threads_rec(*it);
  }
  else if(statement=="goto" ||
          statement=="non-deterministic-goto" ||
          statement=="return" ||
          statement=="decl" ||
          statement=="assign" ||
          statement=="assume" ||
          statement=="assert" ||
          statement=="bp_enforce" ||
          statement=="bp_dead" ||
          statement=="functioncall" ||
          statement=="bp_constrain" ||
          statement=="skip")
  {
  }
  else
  {
    std::cerr << "unexpected statement: " << code << std::endl;
    assert(false);
  }
}

/*******************************************************************\

Function: convert_to_promelat::do_indent

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promelat::do_indent(unsigned indent)
{
  for(unsigned i=0; i<indent; i++)
    out << "  ";
}

/*******************************************************************\

Function: convert_to_promelat::convert_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promelat::convert_expr(const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);
    const contextt::symbolst::const_iterator s_it=
      context.symbols.find(identifier);

    if(s_it==context.symbols.end())
    {
      std::cerr << "failed to find symbol "
                << expr.pretty() << std::endl;
      assert(false);
    }
    
    const symbolt &symbol=s_it->second;
    
    out << "var_" << symbol.base_name;
  }
  else if(expr.id()=="next_symbol")
  {
    const irep_idt &identifier=expr.get("identifier");

    const next_symbol_mappingt::const_iterator m_it=
      next_symbol_mapping.find(identifier);

    if(m_it==next_symbol_mapping.end())
    {
      std::cerr << "failed to find next symbol "
                << expr.pretty() << std::endl;
      assert(false);
    }
    
    out << m_it->second;
  }
  else if(expr.id()=="temp_symbol")
  {
    out << expr.get("identifier");
  }
  else if(expr.id()=="constant")
  {
    if(expr.is_true())
    {
      out << "true";
    }
    else if(expr.is_false())
    {
      out << "false";
    }
    else
    {
      std::cerr << "unexpected constant expression: "
                << expr.pretty() << std::endl;
      assert(false);
    }
  }
  else if(expr.id()=="and")
  {
    assert(!expr.operands().empty());

    forall_operands(it, expr)
    {
      bool first=it==expr.operands().begin();
      if(!first) out << " && ";
      if(!is_symbol(*it)) out << "(";
      convert_expr(*it);
      if(!is_symbol(*it)) out << ")";
    }
  }
  else if(expr.id()=="or")
  {
    assert(!expr.operands().empty());

    forall_operands(it, expr)
    {
      bool first=it==expr.operands().begin();
      if(!first) out << " || ";
      
      if(!is_symbol(*it)) out << "(";
      convert_expr(*it);
      if(!is_symbol(*it)) out << ")";
    }
  }
  else if(expr.id()=="xor")
  {
    assert(!expr.operands().empty());

    forall_operands(it, expr)
    {
      bool first=it==expr.operands().begin();
      if(!first) out << " ^ ";
      
      if(!is_symbol(*it)) out << "(";
      convert_expr(*it);
      if(!is_symbol(*it)) out << ")";
    }
  }
  else if(expr.id()=="not")
  {
    assert(expr.operands().size()==1);

    out << "!";
    if(!is_symbol(expr.op0())) out << "(";
    convert_expr(expr.op0());
    if(!is_symbol(expr.op0())) out << ")";
  }
  else
  {
    std::cerr << "unexpected expression: "
              << expr.pretty() << std::endl;
    assert(false);
  }
}

/*******************************************************************\

Function: convert_to_promelat::remove_non_determinism

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promelat::remove_non_determinism(exprt &expr, unsigned indent)
{
  Forall_operands(it, expr)
    remove_non_determinism(*it, indent);

  if(expr.id()=="nondet_bool" || expr.id()=="nondet_choice")
  {
    // introduce new variable for it
    const irep_idt name="temp_"+i2string(++temp_symbol_counter);
    
    out << "skip;  /* non-deterministic choice in expression */" << std::endl;
    out << std::endl;
    
    do_indent(indent);
    out << "bool " << name << ";" << std::endl;
    do_indent(indent);
    
    out << "if"
        << std::endl;
    
    if(expr.id()=="nondet_bool")
    {
      do_indent(indent);
      out << ":: true -> " << name << "=true;" << std::endl;
      do_indent(indent);
      out << ":: true -> " << name << "=false;" << std::endl;
    }
    else if(expr.id()=="nondet_choice")
    {
      forall_operands(it, expr)
      {
        do_indent(indent);
        out << ":: true -> " << name << "=";
        convert_expr(*it); // free of non-determinism
        out << ";" << std::endl;
      }
    }
    
    do_indent(indent);
    out << "fi; /* end of non-deterministic choice */" << std::endl;
    out << std::endl;
    do_indent(indent);
    
    exprt new_expr("temp_symbol");
    new_expr.set("identifier", name);
    
    expr.swap(new_expr);
  }
}

/*******************************************************************\

Function: convert_to_promelat::convert_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promelat::convert_code(const exprt &code,
                                       unsigned indent)
{
  assert(code.id()=="code");

  const irep_idt &statement=code.get("statement");

  do_indent(indent);
  
  if(statement=="label")
  {
    convert_label(code, indent);
  }
  else if(statement=="ifthenelse")
  {
    convert_ifthenelse(code, indent);
  }
  else if(statement=="block")
  {
    out << "{" << std::endl;
    
    forall_operands(it, code)
      convert_code(*it, indent+1);
      
    do_indent(indent);
    out << "}" << std::endl;
    out << std::endl;
  }
  else if(statement=="goto")
  {
    out << "goto LABEL_"
        << code.get("destination") << ";" << std::endl;
    out << std::endl;
  }
  else if(statement=="non-deterministic-goto")
  {
    convert_non_deterministic_goto(code, indent);
  }
  else if(statement=="return")
  {
    convert_return(code, indent);
  }
  else if(statement=="decl")
  {
    convert_decl(code, indent);
  }
  else if(statement=="assign")
  {
    convert_assign(code, indent, true_exprt());
  }
  else if(statement=="bp_constrain")
  {
    convert_constrain(code, indent);
  }
  else if(statement=="assume")
  {
    convert_assume(code, indent);
  }
  else if(statement=="assert")
  {
    convert_assert(code, indent);
  }
  else if(statement=="bp_enforce")
  {
    assert(code.operands().size()==1);

    const exprt &op=code.op0();
    
    if(op.is_true())
    {
      out << "skip; /* enforce TRUE */" << std::endl;
    }
    else
    {
      // do nothing for now
      out << "skip; /* bp_enforce TODO */" << std::endl;
    }
  }
  else if(statement=="bp_abortif")
  {
    // do nothing for now
    out << "skip; /* bp_abortif TODO */" << std::endl;
  }
  else if(statement=="bp_dead")
  {
    // do nothing, SPIN won't benefit
    out << "skip; /* bp_dead */" << std::endl;
  }
  else if(statement=="functioncall")
  {
    convert_functioncall(code, indent,
                         static_cast<const exprt &>(get_nil_irep()));
  }
  else if(statement=="skip")
  {
    out << "skip; /* skip */" << std::endl;
  }
  else if(statement=="bp_start_thread")
  {
    out << "skip; /* bp_start_thread */" << std::endl;
  }
  else
  {
    std::cerr << "unexpected statement: " << code << std::endl;
    assert(false);
  }
}

/*******************************************************************\

Function: convert_to_promelat::convert_return

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promelat::convert_return(const exprt &code,
                                         unsigned indent)
{
  out << "/* return */" << std::endl;
  
  // turn into assignment and goto

  if(!is_main)
  {
    if(number_of_returned_variables==0)
    {
    assert(code.operands().size()==0);
    // just notify
      do_indent(indent);
      out << "return_value!false; /* dummy */" << std::endl;
    }
    else
    {
      assert(code.operands().size()==1);
      const exprt &op=code.op0();
      
      do_indent(indent);

      if(number_of_returned_variables==1)
      {
        exprt new_value(op);
        remove_non_determinism(new_value, indent);
        out << "return_value!";
        convert_expr(new_value);
      }
      else
      {
        assert(op.id()=="bool-vector");
        assert(op.operands().size()==number_of_returned_variables);
        
        std::list<exprt> new_values;
        
        forall_operands(it, op)
        {
          new_values.push_back(*it);
          remove_non_determinism(new_values.back(), indent);
        }

        out << "return_value!";

        for(std::list<exprt>::const_iterator it=
            new_values.begin(); it!=new_values.end(); it++)
        {
          if(it!=new_values.begin()) out << ",";
          convert_expr(*it);
        }        
      }

      out << ";" << std::endl;
    }
  }
  
  do_indent(indent);
  out << "goto return_target;" << std::endl;
  out << std::endl;
}

/*******************************************************************\

Function: convert_to_promelat::convert_label

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promelat::convert_label(const exprt &code,
                                        unsigned indent)
{
  const irep_idt &label=code.get("label");

  assert(code.operands().size()==1);
  
  // first see if it's a duplicate
  if(code.op0().get("statement")=="label" &&
     code.op0().get("label")==label)
  {
    // do nothing
    out << "/* duplicated label */" << std::endl;
    convert_code(code.op0(), indent);
  }
  else if(has_prefix(id2string(label), "ASYNC_"))
  {
    // run thread
    out << std::endl;
    do_indent(indent);

    out << "run fkt_main(THREAD_" << label << ");"
        << std::endl;
        
    // define thread
        
    do_indent(indent);

    out << "if :: false -> LABEL_"
        << label << ":" << std::endl;

    convert_code(code.op0(), indent+1);
    
    out << std::endl;
    do_indent(indent+1);
    out << "goto return_target; /* kill thread */" << std::endl;
    out << std::endl;
    
    do_indent(indent);
    out << ":: true -> skip;" << std::endl;
    do_indent(indent);
    out << "fi; /* end of thread " << label << " */" << std::endl;
    out << std::endl;
  }
  else
  {
    out << "LABEL_"
        << label << ":" << std::endl;

    if(label=="SLIC_ERROR")
    {
      do_indent(indent);
      out << "assert(false);" << std::endl;
    }

    convert_code(code.op0(), indent);
  }
}

/*******************************************************************\

Function: convert_to_promelat::convert_functioncall

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promelat::convert_functioncall(const exprt &code,
                                               unsigned indent,
                                               const exprt &lhs)
{
  // first find the function in the context
  assert(code.operands().size()>=1);
  assert(code.op0().id()==ID_symbol);
  
  const irep_idt &identifier=
    code.op0().get(ID_identifier);
  
  const contextt::symbolst::const_iterator s_it=
    context.symbols.find(identifier);
  
  if(s_it==context.symbols.end())
  {
    std::cerr << "failed to find function "
              << identifier << std::endl;
    assert(false);
  }
  
  const symbolt &symbol=s_it->second;
  
  // run process

  out << "skip; /* call to function " << symbol.base_name
      << " */" << std::endl;
  out << std::endl;

  const irept &argument_types=symbol.type.find("argument_types");
  const typet &return_type=(typet &)symbol.type.find("return_type");
  
  assert(argument_types.get_sub().size()==
         code.operands().size()-1);

  // do actual arguments
  std::list<exprt> actuals;
  
  unsigned i=1;
  forall_irep(it, argument_types.get_sub())
  {
    exprt new_actual(code.operands()[i]);
    remove_non_determinism(new_actual, indent+1);
    actuals.push_back(exprt());
    actuals.back().swap(new_actual);
    i++;
  }

  do_indent(indent); 
  out << "{" << std::endl;
  do_indent(indent+1);
  const std::string return_value="return_value"+i2string(++temp_symbol_counter);
  out << "chan " << return_value << " = [0] of { ";
  
  unsigned nr_ret=vector_width(return_type);
  
  if(nr_ret==0)
  {
    out << "bool }; /* dummy for synchronization */" << std::endl;
    assert(lhs.is_nil());
  }
  else
  {
    for(unsigned i=0; i<nr_ret; i++)
    {
      if(i!=0) out << ", ";
      out << "bool";
    }
    
    out << " };" << std::endl;

    assert(lhs.is_not_nil());
  }

  do_indent(indent+1);
  out << "run fkt_" << symbol.base_name << "(" << return_value;
  
  for(std::list<exprt>::const_iterator it=actuals.begin();
      it!=actuals.end(); it++)
  {
    out << ", ";
    convert_expr(*it);
  }
  
  out << ");" << std::endl;
  
  do_indent(indent+1);
  out << "/* wait for return */" << std::endl;
  
  do_indent(indent+1);
  out << return_value << "?";

  if(nr_ret==0)
    out << "false;" << std::endl;
  else if(nr_ret==1)
  {
    convert_expr(lhs);
    out << ";" << std::endl;
  }
  else
  {
    assert(lhs.operands().size()==nr_ret);

    for(unsigned i=0; i<nr_ret; i++)
    {
      if(i!=0) out << ",";
      convert_expr(lhs.operands()[i]);
    }
    
    out << ";" << std::endl;
  }
  
  do_indent(indent); 
  out << "} /* end of function call */" << std::endl;  
}

/*******************************************************************\

Function: convert_to_promelat::convert_non_deterministic_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promelat::convert_non_deterministic_goto
 (const exprt &code, unsigned indent)
{
  const irept::subt &destinations=code.find("destinations").get_sub();

  out << "if /* non-deterministic goto */" << std::endl;
  
  forall_irep(it, destinations)
  {
    do_indent(indent);
    out << ":: 1 -> goto LABEL_"
        << it->id_string() << ";" << std::endl;
  }

  do_indent(indent);
  out << "fi; /* end of non-deterministic goto */" << std::endl;
  out << std::endl;    
}

/*******************************************************************\

Function: convert_to_promelat::convert_ifthenelse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promelat::convert_ifthenelse(const exprt &code,
                                             unsigned indent)
{
  assert(code.operands().size()==2 ||
         code.operands().size()==3);
         
  out << "if" << std::endl;
  do_indent(indent);
  
  out << ":: ";

  if(code.op0().id()=="nondet_bool")
  {
    out << "true ->" << std::endl;
    
    convert_code(code.op1(), indent+1);
    
    do_indent(indent);
    out << ":: true ->";
    
    if(code.operands().size()==3)
    {
      out << std::endl;
      convert_code(code.operands()[2], indent+1);
    }
    else
      out << " skip;" << std::endl;
  }
  else
  {
    convert_expr(code.op0());      
    out << " ->" << std::endl;
    
    convert_code(code.op1(), indent+1);

    do_indent(indent);
    out << ":: else ->" << std::endl;

    if(code.operands().size()==3)
      convert_code(code.operands()[2], indent+1);
    else
    {
      do_indent(indent+1);
      out << "skip;" << std::endl;
    }
  }

  do_indent(indent);    
  out << "fi;" << std::endl;
}

/*******************************************************************\

Function: convert_to_promelat::convert_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promelat::convert_assign(const exprt &code,
                                         unsigned indent,
                                         const exprt &constraint)
{
  assert(code.operands().size()==2);

  const exprt &lhs=code.op0();
  const exprt &rhs=code.op1();
  
  // first, see if it is a function call
  
  if(rhs.id()=="sideeffect" &&
     rhs.get("statement")=="functioncall")
  {
    convert_functioncall(rhs, indent, lhs);
  }
  else if(lhs.id()=="symbol" && rhs.is_constant() &&
          constraint.is_true())
  {
    convert_expr(lhs);
    out << " = ";
    convert_expr(rhs);
    out << ";" << std::endl;
    out << std::endl;
  }
  else
  {
    next_symbol_mapping.clear();
    exprt final_lhs(lhs), final_rhs(rhs);

    // RHS might have non-determinism    
    remove_non_determinism(final_rhs, indent);

    // we need temporary variables
    out << "atomic { /* assignment */" << std::endl;
    
    const std::string name=
      "temp_"+i2string(++temp_symbol_counter)+"_";
    
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
      const std::string final_name=name+i2string(i+1);

      do_indent(indent+1);
      out << "bool " << final_name << ";" << std::endl;
      do_indent(indent+1);
      out << final_name << " = ";
      convert_expr(final_rhs.operands()[i]);
      out << ";" << std::endl;
      
      assert(final_lhs.operands()[i].id()=="symbol");
      next_symbol_mapping[final_lhs.operands()[i].get("identifier")]=
        final_name;
    }
    
    out << std::endl;
    
    if(!constraint.is_true())
    {
      do_indent(indent+1);
      out << "/* constraint */" << std::endl;
      do_indent(indent+1);
      out << "(";
      convert_expr(constraint);
      out << ");" << std::endl;
      out << std::endl;
    }
    
    // do actual assignment

    for(unsigned i=0; i<nr; i++)
    {
      do_indent(indent+1);
      convert_expr(final_lhs.operands()[i]);
      out << " = " << name << (i+1) << ";" << std::endl;
    }
    
    do_indent(indent);
    out << "} /* end of assignment */" << std::endl;
    out << std::endl;

    next_symbol_mapping.clear();
  }
}

/*******************************************************************\

Function: convert_to_promelat::convert_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promelat::convert_decl(const exprt &code,
                                       unsigned indent)
{
  assert(code.operands().size()==1);
  
  const exprt &op=code.op0();
  assert(op.id()==ID_symbol);

  const irep_idt &identifier=op.get(ID_identifier);
  const contextt::symbolst::const_iterator s_it=
    context.symbols.find(identifier);

  if(s_it==context.symbols.end())
  {
    std::cerr << "failed to find symbol " << identifier
              << std::endl;
    assert(false);
  }

  const symbolt &symbol=s_it->second;

  out << "bool var_" << symbol.base_name << ";" << std::endl;
  out << std::endl;
}

/*******************************************************************\

Function: convert_to_promelat::convert_assume

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promelat::convert_assume(const exprt &code,
                                         unsigned indent)
{
  assert(code.operands().size()==1);

  exprt op(code.op0());

  // might have non-determinism    
  remove_non_determinism(op, indent);

  out << "/* assumption */" << std::endl;
  do_indent(indent);
  out << "(";
  convert_expr(code.op0());
  out << ");" << std::endl;
  out << std::endl;
}

/*******************************************************************\

Function: convert_to_promelat::convert_constrain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promelat::convert_constrain(const exprt &code,
                                            unsigned indent)
{
  assert(code.operands().size()==2);

  const irep_idt &statement=code.op0().get("statement");
  
  if(statement=="assign")
    convert_assign(code.op0(), indent,
                   code.op1());
  else
    assert(false);
}

/*******************************************************************\

Function: convert_to_promelat::convert_assert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promelat::convert_assert(const exprt &code,
                                         unsigned indent)
{
  assert(code.operands().size()==1);

  exprt op(code.op0());

  // might have non-determinism    
  remove_non_determinism(op, indent);

  out << "/* assertion */" << std::endl;
  
  do_indent(indent);
  out << "assert(";
  convert_expr(code.op0());
  out << ");" << std::endl;
  out << std::endl;
}

/*******************************************************************\

Function: convert_to_promelat::find_threads

  Inputs:

 Outputs:

 Purpose: produce #define's for threads

\*******************************************************************/

void convert_to_promelat::find_threads(const exprt &code)
{
  out << std::endl;
  out << "/* Thread Identifiers */" << std::endl;
  out << std::endl;
  
  out << "#define MAIN 0" << std::endl;

  find_threads_rec(code);
  
  unsigned count=1;
  
  for(threadst::const_iterator it=threads.begin();
      it!=threads.end(); it++)
    out << "#define THREAD_" << *it << " " << count++
        << std::endl;
  
  out << std::endl;
}

/*******************************************************************\

Function: convert_to_promelat::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promelat::convert()
{
  out << "/* Generated automatically by BOPPO */" << std::endl;
  out << std::endl;

  convert_global_variables();  

  convert_functions();
  
  // generate init process
  
  out << "/* initialization */" << std::endl;
  out << std::endl;

  out << "init { run fkt_main(MAIN); }";
  out << std::endl;  
}

/*******************************************************************\

Function: convert_to_promela

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert_to_promela(const contextt &context,
                        std::ostream &out)
{
  convert_to_promelat convert_to_promela(context, out);
  
  convert_to_promela.convert();
}

