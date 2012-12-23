/*******************************************************************\

Module: Ranking Function Synthesis (Rankfinder backend)

Author: CM Wintersteiger

Date: May 2009

\*******************************************************************/

#include <memory>
#include <fstream>
#include <iostream>
#include <cstdlib>

#include <std_expr.h>
#include <arith_tools.h>
#include <simplify_expr.h>
#include <i2string.h>
#include <find_symbols.h>
#include <prefix.h>
#include <config.h>
#include <replace_symbol.h>

#include <langapi/language_util.h>

#include "rankfunction_typecheck.h"

#include "ranking_rankfinder.h"

class expr2rankfindert
{
public:
  expr2rankfindert() {}
  ~expr2rankfindert() {}

  class UnhandledException
  {
  public:
    exprt reason;
    UnhandledException(exprt r) : reason(r) {};
  };

  std::string operator()(const exprt &e, 
                         bool negated=false,
                         bool bool_context=false) const
  {
    return convert_rec(e, negated, bool_context);
  }

protected:                      
  std::string convert_rec(const exprt &e, 
                          bool negated=false,
                          bool bool_context=false) const;
};

/********************************************************************\

 Function: ranking_synthesis_rankfindert::instantiate_template

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking_synthesis_rankfindert::instantiate(void)
{
  exprt path = body.body_relation;
  propagate_expressions(path);

  if(!write_input_file(path))
    return nil_exprt();

  // make sure nothing is saved
  rank_relation = false_exprt();

  return true_exprt();
}

/*******************************************************************\

 Function: ranking_synthesis_rankfindert::generate_functions

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_rankfindert::generate_functions(void)
{
  #if 0
  std::cout << "GENERATE: " << templ << std::endl;
  #endif


  if(instantiate()==nil_exprt())
    return false;

  status("Calling rankfinder...");
  fine_timet before = current_time();
  system("rankfinder rankfinder.input 1> rankfinder.out 2> rankfinder.err");
  solver_time += current_time()-before;
  solver_calls++;

  if(!read_output()) throw "RANKFINDER ERROR";

//  remove("rankfinder.input");
  remove("rankfinder.err");
  remove("rankfinder.out");

  if(coefficients.size()>0)
  {
    if(!extract_ranking_relation())
      return false;

    return true;
  }
  else
    return false;
}

/*******************************************************************

 Function: ranking_synthesis_rankfindert::extract_functions

 Inputs:

 Outputs:

 Purpose:

 \********************************************************************/

bool ranking_synthesis_rankfindert::extract_ranking_relation(void)
{
  exprt function = false_exprt();
  replace_symbolt post_replace_map;

  std::string rank_string;

  unsigned inx=0;
  bool first=true;
  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    if(used_variables.find(it->first)==used_variables.end())
      continue;
    
    exprt postsym=symbol_exprt(it->first, ns.lookup(it->first).type);
    exprt presym=symbol_exprt(it->second, ns.lookup(it->second).type);
    
    post_replace_map.insert(it->second, postsym);

    if(first)
      first=false;
    else
      rank_string+= " + ";

    rank_string+=integer2string(coefficients[inx]);
    rank_string+="*I" + i2string(inx+1);
    inx++;
  }

  for(intermediate_statet::const_iterator it=intermediate_state.begin();
      it!=intermediate_state.end();
      it++)
  {
    if(has_prefix(id2string(*it), "symex::invalid_object") ||
       has_prefix(id2string(*it), "symex_dynamic"))
       continue;
    
    rank_string+= " + ";

    rank_string+=integer2string(coefficients[inx]);
    rank_string+="*I"+i2string(inx+1);

    inx++;
  }

  if(bound!=0)
  {
    rank_string = "(" + rank_string + ")-(" + integer2string(bound) + ")";
  }

  std::cout << "RANKSTRING: " << rank_string << std::endl;

  if(parse_rank_function(rank_string, trans_context, ns, *message_handler, function))
    throw ("RF EXTRACTION ERROR");

  variable_map.replace(function);

  simplify(function, ns);

  exprt post_function = function;
  post_replace_map.replace(post_function);

  rank_relation = binary_relation_exprt(post_function, "<", function);

  return true;
}

/*******************************************************************

 Function: ranking_synthesis_rankfindert::propagate_expressions

 Inputs:

 Outputs:

 Purpose: Propagates all RHS expressions into the LHS such that all
          assignments can be assumed to be executed in parallel.

\********************************************************************/

void ranking_synthesis_rankfindert::propagate_expressions(exprt &e)
{
  assert(e.id()==ID_and && e.type()==bool_typet());

  // first split top-level ands.
  bool progress=true;
  while(progress)
  {
    progress=false;
    and_exprt t;
    forall_operands(it, e)
    {
      if (it->id()!=ID_and)
        t.copy_to_operands(*it);
      else
      {
        forall_operands(iit, *it)
          t.copy_to_operands(*iit);
        progress=true;
      }
    }
    e = t;
  }

  replace_mapt map;

  forall_operands(it, e)
  {
    if(it->id()==ID_equal)
    {
      assert(it->operands().size()==2);
      map[it->op0()] = it->op1();
    }
  }

  Forall_operands(it, e)
  {
    if(it->id()==ID_equal)
    {
      replace_expr(map, it->op1());
    }
    else
      replace_expr(map, *it);
  }

}

/*******************************************************************

 Function: ranking_synthesis_rankfindert::write_input_file

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_rankfindert::write_input_file(const exprt &e)
{
  assert(e.id()==ID_and && e.type()==bool_typet());

  std::ofstream f("rankfinder.input");
  f << "relation(" << std::endl;

  exprt e_ext = e;
  replace_symbolt rmap;

  std::set<irep_idt> inputs, outputs;

  collect_variables(e_ext, rmap, inputs, outputs);

  // write variable declarations
  write_variables(f, inputs, outputs);
  f << ", " << std::endl;

  // translate constraints
  if(!write_constraints(f, rmap, e_ext))
    return false;

  f << ", space(int), dump('rf_result.txt')";
  f << ")." << std::endl;

  f.close();

  return true;
}

/*******************************************************************\

 Function: expr2rankfindert::convert_rec

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

std::string expr2rankfindert::convert_rec(
  const exprt &e, 
  bool negated,
  bool bool_context) const
{
  assert(e.id()!=ID_nil);

  if(e.id()==ID_symbol)
  {
    if(bool_context && negated)
      return e.get_string(ID_identifier) + " = 0";
    else if(bool_context && !negated)
      return e.get_string(ID_identifier) + " =\\= 0";
    else
      return e.get_string(ID_identifier);
  }
  else if(e.id()==ID_not)
  {
    assert(e.operands().size()==1);
    
    if(e.op0().id()==ID_or)
    {
      exprt t(ID_and);
      forall_operands(it, e.op0())
      {
        t.copy_to_operands(*it);
        t.operands().back().make_not();
      }
      
      return convert_rec(t, negated, true);
    }
    else
      return convert_rec(e.op0(), !negated, true);
  }
  else if(e.id()==ID_and && !negated)
  {
    std::string res;
    
    forall_operands(it, e)
    {
      res+=convert_rec(*it, false, true);
      if(it!=--e.operands().end()) res+=", ";
    }
    
    return res;
  }
  else if(e.id()==ID_equal || e.id()==ID_lt ||
          e.id()==ID_gt || e.id()==ID_notequal ||
          e.id()==ID_ge || e.id()==ID_le)
  {
    assert(e.operands().size()==2);
    std::string a = convert_rec(e.op0());
    std::string b = convert_rec(e.op1());

    if((e.id()==ID_equal && !negated) || (e.id()==ID_notequal && negated))
      return a + " = " + b;
    else if((e.id()==ID_equal && negated) || (e.id()==ID_notequal && !negated))
      return a + " =\\= " + b;
    else if((e.id()==ID_le && !negated) || (e.id()==ID_gt && negated))
      return a + " =< " + b;
    else if((e.id()==ID_lt && !negated) || (e.id()==ID_ge && negated))
      return a + " < " + b;
    else if((e.id()==ID_ge && !negated) || (e.id()==ID_lt && negated))
      return a + " >= " + b;
    else if((e.id()==ID_gt && !negated) || (e.id()==ID_le && negated))
      return a + " > " + b;
    else
      throw "NYI:" + e.id_string();
  }
  else if(e.id()==ID_plus || e.id()==ID_mult)
  {
    std::string res;
    forall_operands(it, e)
    {
      if(it!=e.operands().begin()) res += " " + e.id_string() + " ";
      res += convert_rec(*it);
    }
    return res;
  }
  else if(e.id()==ID_minus)
  {
    assert(e.operands().size()==2);
    return convert_rec(e.op0()) + " - " + convert_rec(e.op1());
  }
  else if(e.id()==ID_unary_minus)
  {
    assert(e.operands().size()==1);
    return std::string("-(") + convert_rec(e.op0()) + ")";
  }
  else if(e.id()==ID_constant)
  {
    mp_integer mi;
    to_integer(e, mi);
    return integer2string(mi);
  }
  else if(e.id()==ID_typecast)
  {
    assert(e.operands().size()==1);    
    return convert_rec(e.op0(), negated, bool_context);    
  }
  else if(e.id()==ID_nondet_symbol)
  {
    return "ANY";
  }
  else
    throw UnhandledException(e);
}

/*******************************************************************

 Function: ranking_synthesis_rankfindert::read_output

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_rankfindert::read_output(void)
{
  std::ifstream in("rankfinder.out");
  coefficients.clear();

  bool result_found=false;
  while(in)
  {
    std::string line;

    std::getline(in, line);

    if(line.substr(0,16)=="not well-founded" ||
       line.substr(0,21)=="No linear rank exists")
    {
      return true;
    }
    else if(line.substr(0,7)=="Ranking")
    {
      std::vector<std::string> tokens;
      tokenize(line, tokens, " =[],\tr");

      bool work=false;
      for(std::vector<std::string>::const_iterator it=tokens.begin();
          it!=tokens.end();
          it++)
      {
        //std::cout << "TOKEN: " << *it << std::endl;

        if(*it=="Ranking")
        {
          result_found=true;
          work=true;
        }
        else if(work)
        {
          coefficients.push_back(mp_integer());
          coefficients.back() = string2integer(*it);
        }
      }
    }
    else if(line.substr(0,10)=="Bounded by")
    {
      std::vector<std::string> tokens;
      tokenize(line, tokens, " =[],\t");

      for(std::vector<std::string>::const_iterator it=tokens.begin();
          it!=tokens.end();
          it++)
      {
        //std::cout << "TOKEN: " << *it << std::endl;

        if(*it=="Bounded" || *it=="by" || *it=="d0")
          continue;
        else
        {
          bound = string2integer(*it);
        }
      }
    };
  }

  if(!result_found) return false;

  std::cout << "Coefficients: [";
  for(std::vector<mp_integer>::const_iterator it=coefficients.begin();
      it!=coefficients.end();
      it++)
  {
    if(it!=coefficients.begin()) std::cout << ",";
    std::cout << *it;
  }
  std::cout << "]" << std::endl;

  std::cout << "Bound: " << bound << std::endl;

  return true;
}

/*******************************************************************

 Function: ranking_synthesis_rankfindert::write_variables

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_rankfindert::write_variables(
  std::ostream &f,
  const std::set<irep_idt> &inputs,
  const std::set<irep_idt> &outputs) const
{
  f << " from(";
  for (std::set<irep_idt>::const_iterator it=inputs.begin();
       it!=inputs.end();
       it++)
  {
    if(it!=inputs.begin()) f << ", ";
    f << *it;
  }
  f << "), " << std::endl;

  f << " to(";
  for (std::set<irep_idt>::const_iterator it=outputs.begin();
       it!=outputs.end();
       it++)
  {
    if(it!=outputs.begin()) f << ", ";
    f << *it;
  }
  f << ")";
}

/*******************************************************************

 Function: ranking_synthesis_rankfindert::write_constraints

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool ranking_synthesis_rankfindert::write_constraints(
  std::ostream &f,
  replace_symbolt &rmap,
  const exprt &e)
{
  expr2rankfindert expr2rankfinder;
  f << " constraint([";

  std::cout << "CONSTRAINTS:" << std::endl;

  bool first=true;
  forall_operands(it, e)
  {
    exprt t = *it;
    std::cout << from_expr(ns, "", *it) << std::endl;

    rmap.replace(t);

    {
      if(!first) f << ", ";

      try {
        
        // special cases of division are rewritten...
        // a general method would be preferred, of course.
        if(t.id()==ID_equal &&
           t.operands().size()==2 &&
           t.op1().id()==ID_plus &&
           t.op1().op1().id()==ID_unary_minus &&
           t.op1().op1().op0().id()==ID_div &&
           t.op1().op1().op0().op1().id()==ID_constant)
        {
            exprt c = t.op1().op1().op0().op1();
            exprt l = t.op1().op1().op0().op0();
            t.op1().op1().op0() = l;
            exprt m1 = mult_exprt(t.op1().op0(), c);
            t.op1().op0() = m1;
            exprt m2 = mult_exprt(t.op0(), c);
            t.op0() = m2;
            
            std::cout << "REWRITTEN: " << t << std::endl;
        }
        else if(t.id()==ID_equal &&
            t.operands().size()==2 &&
            t.op1().id()==ID_div &&            
            t.op1().op1().id()==ID_constant)
         {
             exprt c = t.op1().op1();
             exprt l = t.op1().op0();
             t.op1() = l;
             exprt m1 = mult_exprt(t.op0(), c);             
             t.op0() = m1;
             
             std::cout << "REWRITTEN: " << t << std::endl;
         }
          
        f << expr2rankfinder(t, false, true);
        first=false;
      }
      catch (const expr2rankfindert::UnhandledException &ex)
      {
        status("Rankfinder unsuitable: " + ex.reason.id_string());
        status("In: " + from_expr(ns, "", *it));
        return false;
        first = true;
      }
    }
  }

  f << "])";

  return true;
}

/*******************************************************************

 Function: ranking_synthesis_rankfindert::collect_variables

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void ranking_synthesis_rankfindert::collect_variables(
  exprt &e_ext,
  replace_symbolt &rmap,
  std::set<irep_idt> &inputs,
  std::set<irep_idt> &outputs)
{
  unsigned v=1;

  // collect inputs/outputs
  for(bodyt::variable_mapt::const_iterator it=body.variable_map.begin();
      it!=body.variable_map.end();
      it++)
  {
    if(used_variables.find(it->first)==used_variables.end())
    {
      std::cout << "UNUSED: " << it->first << std::endl;
      continue;
    }
    
    exprt postsym=symbol_exprt(it->first, ns.lookup(it->first).type);
    exprt presym=symbol_exprt(it->second, ns.lookup(it->second).type);
    const typet &final_type=ns.follow(presym.type());
        
    irep_idt ident = it->second;
    irep_idt newi = std::string("I") + i2string(v);
    exprt newsym=symbol_exprt(newi, final_type);
    rmap.insert(ident, newsym);
    inputs.insert(newi);

    irep_idt revident=std::string("c::") + id2string(newi);
    variable_map.insert(revident, presym);
    
    symbolt s;
    s.name = revident;
    s.base_name = newi;
    s.type = final_type;
    trans_context.move(s);

    ident = it->first;
    newi = std::string("O") + i2string(v++);
    rmap.insert(ident, symbol_exprt(newi, postsym.type()));
    outputs.insert(newi);

    if(final_type.id()==ID_unsignedbv)
    {
      e_ext.copy_to_operands(binary_relation_exprt(
                    presym, ID_ge, from_integer(0, final_type)));
      e_ext.copy_to_operands(binary_relation_exprt(
                    presym, ID_le, from_integer(-1, final_type)));
    }
    else if(final_type.id()==ID_signedbv)
    {
      unsigned w = safe_width(presym, ns);
      assert(w>0);
      mp_integer limit=power(2, w-1);

      e_ext.copy_to_operands(binary_relation_exprt(
                    presym, ID_ge, from_integer(-limit, final_type)));
      e_ext.copy_to_operands(binary_relation_exprt(
                    presym, ID_le, from_integer(limit-1, final_type)));
    }
    else if(final_type.id()==ID_bool)
    {
      e_ext.copy_to_operands(binary_relation_exprt(
                    presym, ID_ge, from_integer(0, final_type)));
      e_ext.copy_to_operands(binary_relation_exprt(
                    presym, ID_le, from_integer(1, final_type)));
    }
    else if(final_type.id()==ID_pointer)
    {
      unsigned w=config.ansi_c.pointer_width;
      mp_integer limit=power(2, w-1);
      
      e_ext.copy_to_operands(binary_relation_exprt(
                    presym, ID_ge, from_integer(0, unsignedbv_typet(w))));
      e_ext.copy_to_operands(binary_relation_exprt(
                    presym, ID_le, from_integer(-1, unsignedbv_typet(w))));
    }
    else
    {
      unsigned w = safe_width(presym, ns);
      assert(w>0);

      e_ext.copy_to_operands(binary_relation_exprt(
                    presym, ID_ge, from_integer(0, unsignedbv_typet(w))));
      e_ext.copy_to_operands(binary_relation_exprt(
                    presym, ID_le, from_integer(-1, unsignedbv_typet(w))));
    }
  }

  // collect intermediates
  for(intermediate_statet::const_iterator it=intermediate_state.begin();
      it!=intermediate_state.end();
      it++)
  {
    if(has_prefix(id2string(*it), "symex::invalid_object") ||
       has_prefix(id2string(*it), "symex_dynamic"))
       continue;
    
    bool is_symex_id=has_prefix(id2string(*it), "symex::");
    bool is_nondet=has_prefix(id2string(*it), "symex::nondet");
    irep_idt orig_ident;
    exprt sym;
    
    if(is_symex_id)
    {
      orig_ident=*it;
      sym=symbol_exprt(*it, ns.lookup(orig_ident).type);
      
      if(is_nondet) 
        sym.id("nondet_symbol");
    }      
    else
    {
      orig_ident=(id2string(*it).substr(0, id2string(*it).rfind('@')));
      orig_ident=(id2string(orig_ident).substr(0, id2string(orig_ident).rfind('#')));
      sym=symbol_exprt(*it, ns.lookup(orig_ident).type);
    }
    
    // define an input variable for them.
       
    irep_idt newi = std::string("I") + i2string(v); // no v++!

    exprt input_symbol=symbol_exprt(newi, sym.type());
    rmap.insert(*it, input_symbol);
    inputs.insert(newi);

    irep_idt revident=std::string("c::") + id2string(newi);
    variable_map.insert(revident, sym);    

    symbolt s;
    s.name=revident;
    s.base_name=newi;
    s.type=sym.type();
    trans_context.move(s);

    // AND define an output variable.
    irep_idt newo = std::string("O") + i2string(v++);
    outputs.insert(newo);

    if(is_nondet)
    {
      // add a constraint
      exprt os = symbol_exprt(newo, sym.type());
      equal_exprt eq(os,input_symbol);
      e_ext.move_to_operands(eq);
    }
  }
}
