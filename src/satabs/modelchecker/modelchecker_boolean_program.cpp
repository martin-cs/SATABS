/*******************************************************************\

Module: Interface to Model Checkers that use Boolean Programs

Author: Daniel Kroening

  Date: October 2004

\*******************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <ctype.h>

#include <fstream>
#include <list>
#include <algorithm>
#include <sstream>

#include <i2string.h>
#include <substitute.h>
#include <std_expr.h>
#include <string2int.h>

#include "../abstractor/concurrency_aware_abstract_transition_relation.h"

#include "modelchecker_boolean_program.h"

/*******************************************************************\

Function: modelchecker_boolean_programt::read_result_boppo_boom

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool modelchecker_boolean_programt::read_result_boppo_boom(
  std::istream &out1,
  std::istream &out2,
  abstract_modelt &abstract_model,
  abstract_counterexamplet &counterexample)
{
  std::list<std::string> file;

  while(true)
  {
    std::string line;
    if(!std::getline(out1, line)) break;
    file.push_back(line);
  }
  
  // first get result
  
  bool unknown=true, success=false;
  for(std::list<std::string>::const_iterator 
      it=file.begin(); it!=file.end(); it++)
    if(*it=="VERIFICATION SUCCESSFUL")
    {
      success=true; unknown=false;
    }
    else if(*it=="VERIFICATION FAILED")
    {
      read_counterexample_boppo_boom(file, abstract_model, counterexample);
      success=false; unknown=false;
    }
    else if((*it)[0]=='=' &&
        it->find("===[ Problem Statistics ]===")!=std::string::npos)
    {
      for(++it; it!=file.end() && (*it)[0]!='='; ++it)
      {
        assert((*it)[0]=='|');
        std::string::size_type desc_end=it->rfind(".:");
        assert(desc_end!=std::string::npos);
        std::string opt=it->substr(3,desc_end-3);
        assert(*opt.rbegin()=='.');
        std::string::size_type last=opt.size();
        for(--last; last>0 && opt[last]=='.'; --last);
        opt.resize(last+1);
        float val=-1;
        std::istringstream ss(it->substr(desc_end+2, it->size()-desc_end-3));
        ss >> val;
        if(opt=="Non-broadcast assignment operations executed" ||
            opt=="Broadcast assignment operations executed" ||
            opt=="Time spent in non-broadcast assignment operations" ||
            opt=="Time spent in broadcast assignment operations")
        {
          assert(val!=-1);
          assert(stats.find(opt)!=stats.end());
          stats[opt].val+=val;
        }
        else if(opt=="Max number of slots used")
        {
          assert(val!=-1);
          assert(stats.find(opt)!=stats.end());
          if(stats[opt].val<val)
            stats[opt].val=val;
          opt="Total slots";
          assert(stats.find(opt)!=stats.end());
          stats[opt].val+=val;
        }
      }
    }

  if(unknown)
    throw std::string("unexpected result from ")+
      (engine==BOOM?"Boom":"Boppo");
  return success;
}

/*******************************************************************\

Function: modelchecker_boolean_programt::read_counterexample_boppo_boom

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_boolean_programt::read_counterexample_boppo_boom(
  const std::string &line,
  std::list<std::pair<std::string, std::string> > &assignments,
  std::list<std::string> &labels)
{
  for(std::string::size_type p=0; p<line.size();)
  {
    // skip spaces
    while(p<line.size() && line[p]==' ') p++;
    
    if(p>=line.size()) break;

    std::string::size_type p2=p;
    
    // get to next space or '='
    while(p2<line.size() && line[p2]!=' ' && line[p2]!='=')
      p2++;

    if(p2>=line.size() || line[p2]==' ')
    {
      // it's a label
      labels.push_back(std::string(line, p, p2-p));
      p=p2;
    }
    else
    {
      // it's an assignment
      std::string variable(line, p, p2-p);
      
      p=p2+1;

      // get to next space
      while(p2<line.size() && line[p2]!=' ') p2++;
      
      std::string value(line, p, p2-p);
      p=p2;
      
      assignments.push_back(std::pair<std::string, std::string>(
        variable, value));
    }
  }
}


/*******************************************************************\

Function: modelchecker_boolean_programt::read_counterexample_boppo_boom

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_boolean_programt::read_counterexample_boppo_boom(
  const std::list<std::string> &file,
  abstract_modelt &abstract_model,
  abstract_counterexamplet &counterexample)
{
  unsigned thread_count=1;
  unsigned threadbound=max_threads;

  for(std::list<std::string>::const_iterator
      it=file.begin();
      it!=file.end();
      it++)
  {
    const std::string &line=*it;
  
    if(std::string(line, 0, 12)=="threadbound=")
    {
      std::cerr << "THREAD LIMIT line: " << line << std::endl;
      threadbound=safe_str2unsigned(line.c_str()+12);
      std::cerr << "THREAD LIMIT found: " << threadbound << std::endl;
    }
    else if(std::string(line, 0, 6)=="TRACE ")
    {
      abstract_statet abstract_state;

      std::map<unsigned, unsigned> number_of_times_predicate_has_been_seen;
      abstract_stept::predicate_valuest shared_predicate_values;

      shared_predicate_values.resize(abstract_model.variables.size(), false);

      // for gotos
      abstract_state.branch_taken=true;
      
      std::list<std::pair<std::string, std::string> > assignments;
      std::list<std::string> labels;

      // parse      
      read_counterexample_boppo_boom(
        std::string(line, 6, std::string::npos), assignments, labels);
      
      for(std::list<std::string>::const_iterator
          l_it=labels.begin();
          l_it!=labels.end();
          l_it++)
      {
        if(std::string(*l_it, 0, 2)=="PC")
        {
          unsigned PC=safe_str2unsigned(l_it->c_str()+2);
          assert(PC<PC_map.size());
          abstract_state.pc=PC_map[PC];
          abstract_state.label_nr=PC;
          abstract_state.has_pc=true;
        }
      }

      if(!abstract_state.has_pc) continue;
      
      for(std::list<std::pair<std::string, std::string> >::const_iterator
          a_it=assignments.begin();
          a_it!=assignments.end();
          a_it++)
      {
        std::string variable=a_it->first;
        const std::string &value=a_it->second;

        
        // strip function name from variable name
        {
          std::string::size_type pos=variable.find("::");
          if(pos!=std::string::npos)
            variable=std::string(variable, pos+2, std::string::npos);
        }

        if(variable.empty())
          throw "failed to get variable name";
        else if(variable[0]=='b') // checked for emptyness above
        {
          unsigned nr=safe_str2unsigned(variable.c_str()+1);
          if(nr>=abstract_model.variables.size())
            throw "invalid variable in abstract counterexample: "+
              variable;

          if(abstract_model.variables[nr].is_shared_global()) {
        	  shared_predicate_values[nr] = safe_str2int(value.c_str());
          } else {
        	  std::map<unsigned, unsigned>::iterator it = number_of_times_predicate_has_been_seen.insert(std::make_pair(nr, 0)).first;
        	  abstract_stept::thread_to_predicate_valuest::iterator it2 =
        			  abstract_state.thread_states.insert(
        					  std::make_pair(it->second, abstract_stept::predicate_valuest(abstract_model.variables.size(), false))).first;
        	  it2->second[nr] = safe_str2int(value.c_str());
        	  it->second++;
          }
        }
        else if(std::string(variable, 0, 3)=="t")
        {
          abstract_state.thread_nr=safe_str2unsigned(value.c_str());
        }
        else if(variable=="TAKEN")
          abstract_state.branch_taken=safe_str2int(value.c_str());
        else
          throw "unknown variable in abstract counterexample: `"+
                variable+"'";
      }

      assert(abstract_state.thread_states.empty() ||
          abstract_state.thread_states.size() == thread_count ||
          abstract_state.thread_states.size() == threadbound);

      // Plug the shared state into every thread state
      for(unsigned tc=0; tc < thread_count && tc < threadbound; ++tc)
      {
        abstract_stept::thread_to_predicate_valuest::iterator it2 =
          abstract_state.thread_states.insert(
              std::make_pair(tc, abstract_stept::predicate_valuest(abstract_model.variables.size(), false))).first;
    	  for(unsigned i = 0; i < shared_predicate_values.size(); i++)
    	  {
    		  if(abstract_model.variables[i].is_shared_global())
    		  {
    			  it2->second[i] = shared_predicate_values[i];
    		  }
    	  }
      }

      assert(abstract_state.thread_states.size() == thread_count ||
          abstract_state.thread_states.size() == threadbound);

      if(abstract_state.pc->is_start_thread()) ++thread_count;

      counterexample.steps.push_back(abstract_state);
    }
    else if(line=="LOOP [")
    {
      counterexample.steps.push_back(abstract_stept(abstract_stept::LOOP_BEGIN));
    }
    else if(line=="LOOP ]")
    {
      counterexample.steps.push_back(abstract_stept(abstract_stept::LOOP_END));
    }
  }

  assert(!counterexample.steps.empty());
}

/*******************************************************************\

Function: modelchecker_boolean_programt::build_boolean_program_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_boolean_programt::build_boolean_program_file(
  abstract_modelt &abstract_model,
  std::ostream &out)
{
  // start printing Boolean program

  out << "// automatically generated by CPROVER/SATABS\n"
         "\n";

  build_boolean_program_file_global_variables(abstract_model, out);
  build_boolean_program_file_functions(abstract_model, out);
}

/*******************************************************************\

Function: modelchecker_boolean_programt::build_boolean_program_file_local_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_boolean_programt::build_boolean_program_file_local_variables(
  const abstract_modelt &abstract_model,
  std::ostream &out)
{
  #if 0
  //
  // Events
  //

  if(!events.empty())
  {
    out << "-- events\n"
           "\n";

    for(eventst::const_iterator it=events_waited_for.begin();
        it!=events_waited_for.end();
        it++)
    {
      out << "VAR " << "sticky_" << *it
          << ": boolean;" << std::endl;
      out << "ASSIGN init(sticky_" << *it << "):=0;"
          << std::endl;
    }

    out << std::endl;
  }
  #endif
}

/*******************************************************************\

Function: modelchecker_boolean_programt::build_boolean_program_file_global_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_boolean_programt::build_boolean_program_file_global_variables(
  const abstract_modelt &abstract_model,
  std::ostream &out)
{
  //
  // Global program variables
  //

  out << "// variables with procedure-global scope\n"
         "\n";

  size_t max_len=0;

  for(unsigned i=0;
      i<abstract_model.variables.size();
      i++)
    if(abstract_model.variables[i].is_shared_global() ||
       abstract_model.variables[i].is_thread_local())
      max_len=std::max(max_len, variable_names[i].size());

  for(unsigned i=0;
      i<abstract_model.variables.size();
      i++)
    if(abstract_model.variables[i].is_shared_global() ||
       abstract_model.variables[i].is_thread_local())
    {
      out << "decl ";

      if(abstract_model.variables[i].is_thread_local())
        out << "thread_local ";

      out << variable_names[i] << "; ";

      if(abstract_model.variables[i].description!="")
      {
        for(unsigned j=0; j<(max_len+1-variable_names[i].size()); j++)
          out << " ";

        out << "// " << abstract_model.variables[i].description;
      }

      out << std::endl;
    }

  out << std::endl;
  
  //
  // Events
  //

  #if 0
  if(!events.empty())
  {
    out << "-- events\n"
           "\n";

    for(eventst::const_iterator it=events.begin();
        it!=events.end();
        it++)
      out << "VAR " << "event_" << *it
          << ": boolean;" << std::endl;

    out << std::endl;
  }
  #endif
}

/*******************************************************************\

Function: modelchecker_boolean_programt::build_boolean_program_file_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_boolean_programt::build_boolean_program_file_functions(
  abstract_modelt &abstract_model,
  std::ostream &out)
{
  PC_map.clear();

  for(abstract_functionst::function_mapt::iterator
      f_it=abstract_model.goto_functions.function_map.begin();
      f_it!=abstract_model.goto_functions.function_map.end();
      f_it++)
    build_boolean_program_file_function(abstract_model, f_it, out);
}

/*******************************************************************\

Function: modelchecker_boolean_programt::build_boolean_program_file_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_boolean_programt::build_boolean_program_file_function(
  abstract_modelt &abstract_model,
  abstract_functionst::function_mapt::iterator f_it,
  std::ostream &out)
{
  // header
  out << "// " << f_it->first << std::endl;
  out << "void " << convert_function_name(f_it->first)
      << "() begin\n"
         "\n";

  // local variables

  {
    size_t max_len=0;
    bool has_procedure_local_variables=false;

    for(unsigned i=0;
        i<abstract_model.variables.size();
        i++) {
        if(abstract_model.variables[i].is_procedure_local() || abstract_model.variables[i].is_mixed())
        {
          max_len=std::max(max_len, variable_names[i].size());
          has_procedure_local_variables=true;
        }
    }

    if(has_procedure_local_variables)
    {
      out << "      // the procedure-local variables\n"
             "\n";
        
      for(unsigned i=0;
          i<abstract_model.variables.size();
          i++)
        if(abstract_model.variables[i].is_procedure_local() || abstract_model.variables[i].is_mixed())
        {
          out << "  decl " << variable_names[i] << "; ";

          if(abstract_model.variables[i].description!="")
          {
            for(unsigned j=0; j<(max_len+1-variable_names[i].size()); j++)
              out << " ";

            out << "// ";

			if(concurrency_aware)
			{
				if(abstract_model.variables[i].is_procedure_local())
				{
					out << "LOCAL --";
				} else {
					assert(abstract_model.variables[i].is_mixed());
					out << "MIXED --";
				}
				out << " ";
			}

            out << abstract_model.variables[i].description;
          }

          out << std::endl;
        }

      out << std::endl;
    }
  }

  // initialize globals if this is main
  // just to make sure that there is no misunderstanding
  // about the initial value of any global variable

  if(f_it->first=="main")
  {
    out << "      // initialization of the shared-global and thread-local variables\n"
           "\n";

    for(unsigned i=0;
        i<abstract_model.variables.size();
        i++)
      if(abstract_model.variables[i].is_shared_global() ||
         abstract_model.variables[i].is_thread_local())
      {
        out << "      " << variable_names[i] << ":=*; ";
        out << std::endl;
      }

    out << std::endl;
  }

  abstract_programt &abstract_program=f_it->second.body;
  
  // control flow
  
  locationt previous_location;

  for(abstract_programt::instructionst::iterator
      it=abstract_program.instructions.begin();
      it!=abstract_program.instructions.end();
      it++)
  {
    unsigned PC=PC_map.size();
    PC_map.push_back(it);

    if(!it->location.is_nil() &&
       it->location!=previous_location)
    {
      out << "    // " << it->location << std::endl;
      previous_location=it->location;
    }
      
    if(!it->code.get_transition_relation().from_predicates.empty())
    {
      out << "    // FROM Predicates:";
      for(std::set<unsigned>::const_iterator
          p_it=it->code.get_transition_relation().from_predicates.begin();
          p_it!=it->code.get_transition_relation().from_predicates.end();
          p_it++)
        out << " " << variable_names[*p_it];

      out << std::endl;
    }

    if(it->is_target())
    {
      std::string label="l"+i2string(it->target_number);
      out << std::setw(4) << label << ":" << std::endl;
    }

    {
      std::string label="PC"+i2string(PC);
      out << std::setw(4) << label << ": ";
    }

    if(it->is_goto())
    {
      if(!it->guard.is_true())
      {
        out << "if ";

        if(!it->code.get_transition_relation().constraints.size())
          out << expr_string(it->guard);
        else
        {
          exprt &choose=
            it->code.get_transition_relation().constraints.front();

          out << "(schoose[" << expr_string(choose.op0());
          // << " & " << expr_string(it->guard);
          out << "," << expr_string(choose.op1()) <<  "])";
        }
        out << " then ";
      }
      
      out << "goto ";
      
      for(abstract_programt::instructiont::targetst::const_iterator
          gt_it=it->targets.begin();
          gt_it!=it->targets.end();
          gt_it++)
      {
        if(gt_it!=it->targets.begin()) out << ", ";
        out << "l" << (*gt_it)->target_number;
      }
      
      out << ";";

      if(!it->guard.is_true())
        out << " fi;";
    }
    else if(it->is_start_thread())
    {
      out << "start_thread goto ";

      for(abstract_programt::instructiont::targetst::const_iterator
          gt_it=it->targets.begin();
          gt_it!=it->targets.end();
          gt_it++)
      {
        if(gt_it!=it->targets.begin()) out << ", ";
        out << "l" << (*gt_it)->target_number;
      }
      
      out << ";";
    }
    else if(it->is_end_thread())
    {
      out << "end_thread;";
    }
    else if(it->is_assume())
    {
      out << "assume(" << expr_string(it->guard);

      const std::list<exprt> &constraints=
        it->code.get_transition_relation().constraints;
      if(!constraints.empty())
      {
        for(std::list<exprt>::const_iterator
            it=constraints.begin();
            it!=constraints.end();
            it++)
          out << " & " << '(' << expr_string(*it) << ')';
      }
      out << ");";
    }
    else if(it->is_assert())
    {
      out << "assert(" << expr_string(it->guard) << ");";
    }
    else if(it->is_dead())
    {
      out << "dead;";
    }
    else if(it->is_atomic_begin())
    {
      out << "atomic_begin;";
    }
    else if(it->is_atomic_end())
    {
      out << "atomic_end;";
    }
    else if(it->is_other() ||
            it->is_assign() ||
            it->is_decl())
    {
      bool first=true;

      for(unsigned i=0; i<abstract_model.variables.size(); i++)
        if(it->code.get_transition_relation().values.count(i)!=0)
        {
          if(first) first=false; else out << ",";
          out << variable_names[i];
        }

      if(concurrency_aware)
      {
        for(unsigned i=0; i<abstract_model.variables.size(); i++)
        {
          concurrency_aware_abstract_transition_relationt* trans_rel = dynamic_cast<concurrency_aware_abstract_transition_relationt*>(&(it->code.get_transition_relation()));
          assert(NULL != trans_rel);
    		  if(trans_rel->passive_values.count(i)!=0)
          {
            assert(!abstract_model.variables[i].is_thread_local());
            assert(abstract_model.variables[i].is_procedure_local() || abstract_model.variables[i].is_mixed());
    			
            assert(!first);
    			  out << ",";
            exprt tmp=exprt(ID_predicate_passive_symbol, bool_typet());
            tmp.set(ID_identifier, i);
            out << expr_string(tmp);
          }
        }
      }

      if(first) // none changed?
      {
        out << "skip; // no predicates changed";
      }
      else
      {
        out << " := ";

        first=true;

        for(unsigned i=0; i<abstract_model.variables.size(); i++)
        {
          abstract_transition_relationt::valuest::const_iterator
            v_it=it->code.get_transition_relation().values.find(i);
          
          if(v_it!=it->code.get_transition_relation().values.end())
          {
            const exprt &value=v_it->second;

            if(first) first=false; else out << ",";

            if(value.is_nil())
              out << "*";
            else
              out << expr_string(value);
          }
        }

        if(concurrency_aware)
        {
          concurrency_aware_abstract_transition_relationt* trans_rel = dynamic_cast<concurrency_aware_abstract_transition_relationt*>(&(it->code.get_transition_relation()));
          assert(NULL != trans_rel);

          for(unsigned i=0; i<abstract_model.variables.size(); i++)
          {
            abstract_transition_relationt::valuest::const_iterator
              v_it=trans_rel->passive_values.find(i);

            if(v_it!=trans_rel->passive_values.end())
            {
              const exprt &value=v_it->second;

              assert(!first);
              out << ",";

              if(value.is_nil())
                out << "*";
              else
                out << expr_string(value);
            }
          }
        }
        
        // constraints
        
        const std::list<exprt> &constraints=
          it->code.get_transition_relation().constraints;
        
        if(!constraints.empty())
        {
          out << " constrain";
          
          for(std::list<exprt>::const_iterator
              it=constraints.begin();
              it!=constraints.end();
              it++)
          {
            if(it!=constraints.begin()) out << " &";
            out << std::endl << "    "
                << '(' << expr_string(*it) << ')';
          }
        }
          
        out << ";";
      }
    }
    else if(it->is_skip() || it->is_end_function())
    {
      out << "skip;";
    }
    else if(it->is_function_call())
    {
      const code_function_callt &call=
        to_code_function_call(it->code.concrete_pc->code);
      if(call.function().id()!="symbol")
        throw "expected symbol as function argument";
      const symbol_exprt &symbol=to_symbol_expr(call.function());
      const irep_idt &id=symbol.get_identifier();

      out << convert_function_name(id)
          << "();";
    }
    else if(it->is_return())
    {
      out << "return;";
    }
    else if(it->is_location())
    {
      out << "skip; // location only";
    }
    else if(it->is_throw())
    {
      // treat like skip for now
      out << "skip; // throw";
    }
    else if(it->is_catch())
    {
      // treat like skip for now
      out << "skip; // catch";
    }
    else
      throw "unknown statement";

    out << std::endl;

    if(!it->code.get_transition_relation().to_predicates.empty())
    {
      out << "    // TO Predicates:";
      for(std::set<unsigned>::const_iterator
          p_it=it->code.get_transition_relation().to_predicates.begin();
          p_it!=it->code.get_transition_relation().to_predicates.end();
          p_it++)
        out << " " << variable_names[*p_it];

      out << std::endl;
    }

    out << std::endl;
  }
  
  out << "end\n\n";
}

/*******************************************************************\

Function: modelchecker_boolean_programt::expr_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string modelchecker_boolean_programt::expr_string(const exprt &expr)
{
  if(expr.id()==ID_predicate_symbol)
  {
    unsigned p=safe_str2unsigned(expr.get(ID_identifier).c_str());
    assert(p < variable_names.size());
    return variable_names[p];
  }
  else if(expr.id()==ID_predicate_next_symbol)
  {
    unsigned p=safe_str2unsigned(expr.get(ID_identifier).c_str());
    assert(p < variable_names.size());
    return "'"+variable_names[p];
  }
  else if(expr.id()==ID_predicate_passive_symbol)
  {
    unsigned p=safe_str2unsigned(expr.get(ID_identifier).c_str());
    assert(p < variable_names.size());
    return variable_names[p]+"$";
  }
  else if(expr.id()==ID_next_symbol)
  {
    assert(expr.op0().id()==ID_predicate_passive_symbol);
    unsigned p=safe_str2unsigned(expr.op0().get(ID_identifier).c_str());
    assert(p < variable_names.size());
    return "'"+variable_names[p]+"$";
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    return "*";
  }
  else if(expr.id()==ID_implies)
  {
    return "!("+expr_string(expr.op0())+") | ("
               +expr_string(expr.op1())+")";
  }
  else if(expr.id()=="bool-vector")
  {
    std::string dest;

    forall_operands(it, expr)
    {
      if(it!=expr.operands().begin()) dest+=", ";
      dest+=expr_string(*it);
    }

    return dest;
  }
  else if(expr.id()==ID_constant)
  {
    if(expr.is_true())
      return "1";
    else if(expr.is_false())
      return "0";
  }
  else if(expr.id()==ID_equal ||
          expr.id()==ID_and ||
          expr.id()==ID_or) // binary
  {
    bool first=true;
    std::string symbol;
    
    if(expr.id()==ID_equal)
      symbol="="; // boolean!
    else if(expr.id()==ID_and)
      symbol="&";
    else if(expr.id()==ID_or)
      symbol="|";
      
    std::string dest;

    forall_operands(it, expr)
    {
      if(first)
        first=false;
      else
      {
        dest+=' ';
        dest+=symbol;
        dest+=' ';
      }
      
      bool use_paren=
        (expr.id()!=ID_and || expr.id()!=ID_or || expr.id()!=it->id()) &&
        it->id()!=ID_symbol &&
        it->id()!=ID_next_symbol &&
        it->id()!=ID_predicate_symbol &&
        it->id()!=ID_predicate_next_symbol;

      if(use_paren) dest+='(';
      dest+=expr_string(*it);
      if(use_paren) dest+=')';
    }
    
    return dest;
  }
  else if(expr.id()==ID_not)
  {
    std::string dest="!";

    bool use_paren=
      expr.op0().id()!=ID_symbol &&
      expr.op0().id()!=ID_next_symbol &&
      expr.op0().id()!=ID_predicate_symbol &&
      expr.op0().id()!=ID_predicate_next_symbol;

    if(use_paren) dest+='(';
    dest+=expr_string(expr.op0());
    if(use_paren) dest+=')';
    
    return dest;
  }
  else if(expr.id()=="bp_unused")
    return "_";
  else if(expr.id()==ID_nondet_bool)
    return "*";

  // no Boolean Program language expression for internal representation 
  return "??"+expr.id_string()+"??";
}

/*******************************************************************\

Function: modelchecker_boolean_programt::check

  Inputs:

 Outputs:

 Purpose: model check an abstract program using SMV, return
          counterexample if failed
          Return value of TRUE means the program is correct,
          if FALSE is returned, ce will contain the counterexample

\*******************************************************************/

bool modelchecker_boolean_programt::check(
  abstract_modelt &abstract_model,
  abstract_counterexamplet &counterexample)
{
  std::string temp_base="cegar_tmp";

  std::string temp_boolean_program=temp_base+"_abstract.bp";
  std::string temp_boolean_program_out1=temp_base+"_boolean_program_out1";
  std::string temp_boolean_program_out2=temp_base+"_boolean_program_out2";

  build(abstract_model, temp_boolean_program);

  {
    std::string command;

    switch(engine)
    {
    case BOPPO:
      status(std::string("Running BOPPO"));
      command="boppo --compact-trace --por";
      if(loop_detection)
        command+=" --loop-detection";
      break;
      
    case BOOM:
      status(std::string("Running BOOM"));
      command="boom --stats -t";
      
      // boom has a default of 2, which we override
      // with a more reasonable number
      if(max_threads!=0)
        command+=" --threadbound "+i2string(max_threads);
      else
        command+=" --threadbound 5";
      break;
      
    case BEBOP:
      status(std::string("Running BEBOP"));
      throw "Support for Bebop not yet implemented";
      break;
    
    case MOPED:
      status(std::string("Running MOPED"));
      throw "Support for Moped not yet implemented";
      break;
    
    default:
      assert(false);
    }

    command+=" "+temp_boolean_program+" >"+temp_boolean_program_out1+
             " 2>"+temp_boolean_program_out2;

    status(command);

    system(command.c_str());
  }

  {
    std::ifstream out1(temp_boolean_program_out1.c_str()),
                  out2(temp_boolean_program_out2.c_str());

    switch(engine)
    {
    case BOPPO:
    case BOOM:
      return read_result_boppo_boom(
        out1, out2, abstract_model, counterexample);
      break;
    
    default:
      assert(false);
    }
  }

  return false;
}

/*******************************************************************\

Function: modelchecker_boolean_programt::convert_function_name

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

std::string modelchecker_boolean_programt::convert_function_name(
  const irep_idt &name)
{
  std::string result=name.as_string();

  for(unsigned i=0; i<result.size(); i++)
  {
    char ch=result[i];
    if(isalnum(ch) || ch=='_')
    { // ok
    }
    else if(ch==':')
      result[i]='$';
    else
      result[i]='_';
  }

  return result;
}

/*******************************************************************\

Function: modelchecker_boolean_programt::build

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void modelchecker_boolean_programt::build(
  abstract_modelt &abstract_model,
  const std::string &out_file_name)
{
  get_variable_names(abstract_model);
  //get_nondet_symbols(abstract_model);
  //get_events(abstract_model);

  std::ofstream out(out_file_name.c_str());
  build_boolean_program_file(abstract_model, out);
}

/*******************************************************************\

Function: modelchecker_boolean_programt::save

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void modelchecker_boolean_programt::save(
  abstract_modelt &abstract_model,
  unsigned sequence)
{
  build(abstract_model, "satabs."+i2string(sequence)+".bp");
}

/*******************************************************************\

Function: modelchecker_boolean_programt::get_variable_names

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/*
void modelchecker_boolean_programt::get_variable_names(
  const abstract_modelt &abstract_model)
{
  modelcheckert::get_variable_names(abstract_model);

  if(concurrency_aware)
  {
	  passive_variable_names.clear();

	  for(unsigned i=0;
		  i<abstract_model.variables.size();
		  i++)
	  {
		  assert(!abstract_model.variables[i].is_thread_local());
		  if(abstract_model.variables[i].is_procedure_local() || abstract_model.variables[i].is_mixed())
		  {
			  passive_variable_names.push_back(variable_names[i] + "$");
		  }
	  }

  }



}
*/


