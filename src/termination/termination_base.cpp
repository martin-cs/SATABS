/*******************************************************************\

Module: Termination base class

Author: CM Wintersteiger

\*******************************************************************/

#include <string>
#include <sstream>
#include <cstdlib>
#include <algorithm>

#include <find_symbols.h>
#include <prefix.h>
#include <expr_util.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

#include <goto-programs/write_goto_binary.h>

#include <goto-symex/symex_target_equation.h>
#include <goto-symex/goto_symex.h>

#include <satabs/refiner/select_refiner.h>
#include <satabs/refiner/refiner.h>
#include <satabs/abstractor/select_abstractor.h>
#include <satabs/abstractor/abstractor.h>
#include <satabs/modelchecker/select_modelchecker.h>
#include <satabs/modelchecker/modelchecker.h>
#include <satabs/simulator/select_simulator.h>
#include <satabs/simulator/simulator.h>
#include <satabs/satabs_safety_checker.h>

#include "find_symbols_rw.h"
#include "replace_identifier.h"
#include "termination_base.h"

const std::string termination_prefix="termination::pre::";

class custom_symext:
  public goto_symext
{
public:
  custom_symext(const namespacet &_ns,
                contextt &_new_context,
                symex_targett &_target):
    goto_symext(_ns, _new_context, _target)
  {
  }

  bool has_remaining_claims() const { return remaining_claims!=0; }
};

/********************************************************************\

 Function: termination_baset::termination_baset

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

termination_baset::termination_baset(
  const cmdlinet &_cmd,
  const goto_functionst &_gf,
  const contextt &_ctxt,
  class contextt &_sctxt,
  class value_set_analysist &_vsa,
  class invariant_propagationt &_ip,
  message_handlert &_mh,
  ui_message_handlert::uit _ui):
    messaget(_mh),    
    context(_ctxt),
    shadow_context(_sctxt),
    cmdline(_cmd),
    ns(_ctxt, _sctxt),
    ui(_ui),
    goto_functions(_gf),
    value_set_analysis(_vsa),
    invariant_propagation(_ip),
    start_time(current_time()),
    ranking_time(0),    
    modelchecker_time(0),
    counter_example_extraction_time(0),
    final_check_time(0),
    ranksynth_calls(0),
    total_loops(0),
    nonterminating_loops(0),
    nondet_counter(0)
{
  set_verbosity(6);
  if(cmdline.isset("v"))
    set_verbosity(atoi(cmdline.getval("v")));    
  set_options();
}

/********************************************************************\

 Function: termination_baset::adjust_assertion

 Inputs:

 Outputs:

 Purpose: Adjust assertion

\*******************************************************************/

void termination_baset::adjust_assertion(
  const exprt &expr,
  goto_tracet &trace)
{
  status("Adjusting termination assertion.");

  if(trace.steps.empty())
    throw "counterexample is too short";

  goto_trace_stept &assertion=trace.steps.back();

  assert(assertion.is_assert());

  // HACK: nasty cast!
  goto_programt::targett &orig_assertion=
      (*((goto_programt::targett*)(&assertion.pc)));

  exprt &guard=orig_assertion->guard;
  assert(guard.id()=="=>" && guard.operands().size()==2);

  if(expr.is_true()) // to cancel the termination check
  {
    guard.make_true();
  }
  else if(guard.op1().id()=="or")
  {
    guard.op1().copy_to_operands(expr);
  }
  else
  {
    or_exprt new_rel;
    new_rel.move_to_operands(guard.op1());
    new_rel.copy_to_operands(expr);

    guard.op1()=new_rel;
  }

  debug("NEW ASSERTION: " + from_expr(ns, "", guard));
}

/********************************************************************\

 Function: termination_baset::show_loop_trace

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void termination_baset::show_loop_trace(
  const goto_tracet &goto_trace,
  goto_tracet::stepst::const_iterator &loop_begin)
{
  if(verbosity<9) return;
  std::string output;

  output = "--- LOOP TRACE START\n";
  for(goto_tracet::stepst::const_iterator step=loop_begin;
      step!=goto_trace.steps.end();
      step++)
  {
    switch(step->type)
    {
      case goto_trace_stept::ASSIGNMENT:
        output+=from_expr(ns, "", step->pc->code) + "\n";
        break;

      case goto_trace_stept::ASSUME:
        output+=from_expr(ns, "", step->pc->guard) + " [" +
                (step->cond_value?"":"!") + from_expr(ns, "", step->cond_expr) + "]\n";
        break;

      default:
        break;
    }
  }
  output+="--- LOOP TRACE END\n";

  debug(output);
}

/********************************************************************\

 Function: termination_baset::get_ssa_body

 Inputs:

 Outputs:

 Purpose: Compute SSA-like expression for loop body

 \*******************************************************************/

bodyt termination_baset::get_body(
  goto_tracet::stepst::const_iterator &loop_begin,
  const goto_tracet &trace)
{
  bodyt result_body;
  exprt::operandst op;
  const goto_trace_stept &assertion=trace.steps.back();

  // let's get a loop number as well:
  assert(assertion.pc->guard.id()=="=>");
  std::string c_str = assertion.pc->guard.op0().get_string("identifier");
  std::string prefix = termination_prefix+
                       c_str.substr(c_str.rfind("_")+1) + "::";

  // find out what we actually need
  required_stepst required_steps;
  find_required_steps(trace, loop_begin, required_steps, prefix);

  /* We perform a new SSA-conversion. However, since we can only
     get a single path through the program, there are no joins and
     thus no phi-functions. We just increment counters. */

  std::map<irep_idt, unsigned> ssa_counters;
  replace_idt replace_id;

  // get the required body constraints
  for(goto_tracet::stepst::const_iterator step=loop_begin;
      step!=--trace.steps.end();
      step++)
  {
    last_path.push_back(step->pc);

    // required_stepst::const_iterator fit=required_steps.find(&(*step));
    // if(fit==required_steps.end()) continue;

    switch(step->pc->type)
    {
      case ASSIGN:
      {
        const code_assignt &code=to_code_assign(step->pc->code);
        find_symbols_sett w;
        find_symbols_w(code.lhs(), w);

        equal_exprt equality(code.lhs(), code.rhs());
        replace_id.replace(equality.rhs());

        // All the written ones get their SSA-ID updated
        for(find_symbols_sett::const_iterator it=w.begin();
            it!=w.end();
            it++)
        {
          // Are we writing a pre-variable?
          if(has_prefix(id2string(*it), prefix))
          {
            assert(code.rhs().id()==ID_symbol);
            const irep_idt &post_id=code.rhs().get(ID_identifier);
            const irep_idt &pre_id=code.lhs().get(ID_identifier);
            result_body.variable_map[post_id]=pre_id;

            // the RHS gets a #0 id
            irep_idt new_id=id2string(post_id)+"!0";
            replace_id.insert(post_id, new_id);
            equality.rhs().set(ID_identifier, new_id);
          }
          else
          {
            const irep_idt &old_id=*it;
            unsigned cur=++ssa_counters[old_id]; // 0 is never used

            // gets a new ID
            irep_idt new_id=id2string(old_id)+"!"+i2string(cur);
            replace_id.insert(old_id, new_id);
          }
        }

        replace_id.replace(equality.lhs());
        op.push_back(equality);
        break;
      }
      case ASSUME:
      case ASSERT:
      {
        if(!step->cond_expr.is_true() && !step->cond_expr.is_nil())
        {
          exprt guard=step->cond_expr; // That's SSA!
          remove_ssa_ids(guard);
//          exprt guard=step->pc->guard;

          find_symbols_sett syms;
          find_symbols(guard, syms);

          for(find_symbols_sett::const_iterator it=syms.begin();
              it!=syms.end();
              it++)
          {
            if(ssa_counters.find(*it)==ssa_counters.end())
            {
              irep_idt new_id=id2string(*it)+"!"+i2string(++ssa_counters[*it]);
              replace_id.insert(*it, new_id);
            }
          }

          replace_id.replace(guard);
          if(!step->cond_value) guard.negate();
          op.push_back(guard);
        }
        break;
      }
      case GOTO:
      {
        if(!step->cond_expr.is_nil())
        {
//          exprt guard=step->pc->guard;
          exprt guard=step->cond_expr;
          remove_ssa_ids(guard);

          find_symbols_sett syms;
          find_symbols(guard, syms);

          for(find_symbols_sett::const_iterator it=syms.begin();
              it!=syms.end();
              it++)
          {
            if(ssa_counters.find(*it)==ssa_counters.end())
            {
              ssa_counters[*it]=0;
              irep_idt new_id=id2string(*it)+"!"+i2string(0);
              replace_id.insert(*it, new_id);
            }
          }

          replace_id.replace(guard);
          if(!step->cond_value)
            guard.negate();
          op.push_back(guard);
        }
        break;
      }
      case DECL: /* nothing */ break;
	    case LOCATION: /* These can show up here? */ break;
      default:
        throw std::string("unexpected instruction type.");
    }
  }

  // the final result, which (again) contains SSA variables
  exprt &body_expr = result_body.body_relation;
  body_expr = and_exprt(op);

  if(result_body.variable_map.empty())
  {
    // used to be:
    // throw "BUG: No variables found; path missing.";
    // Though: No variable is ever saved, i.e., this loop
    // must be completely nondeterministic.
    warning("No pre-variables found; this "
            "loop is completely non-deterministic.");
    body_expr=false_exprt();
  }

  // The last SSA-occurrence of a variable is the
  // output variable and it gets its non-SSA name.
  replace_idt last_map;
  for(std::map<irep_idt, unsigned>::const_iterator it=ssa_counters.begin();
      it!=ssa_counters.end();
      it++)
  {
    const irep_idt &id=it->first;
    unsigned last=it->second;

    irep_idt last_name=id2string(id)+"!"+i2string(last);
    last_map.insert(last_name, id);
  }

  last_map.replace(body_expr);

  replace_nondet_sideeffects(body_expr);

  return result_body;
}

/*******************************************************************\

Function: termination_baset::replace_nondet_sideeffects

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_baset::replace_nondet_sideeffects(exprt &expr)
{
  if(expr.id()=="sideeffect" &&
     expr.get("statement")=="nondet")
  {
    symbolt symbol;
    symbol.name=std::string("termination::nondet")+i2string(++nondet_counter);
    symbol.base_name=std::string("nondet")+i2string(nondet_counter);
    symbol.type=expr.type();

    expr=symbol_expr(symbol);
    shadow_context.move(symbol);
  }
  else
    Forall_operands(it, expr)
      replace_nondet_sideeffects(*it);
}

/********************************************************************\

 Function: termination_baset::remove_ssa_ids

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void termination_baset::remove_ssa_ids(exprt &expr) const
{
  if(expr.id()==ID_symbol)
  {
    irep_idt ident=expr.get(ID_identifier);
    ident = id2string(ident).substr(0, id2string(ident).rfind('@'));
    ident = id2string(ident).substr(0, id2string(ident).rfind('!'));
    expr.set(ID_identifier, ident);
  }

  Forall_operands(it, expr)
    remove_ssa_ids(*it);
}

/********************************************************************\

 Function: termination_baset::find_required_steps

 Inputs:

 Outputs:

 Purpose: finds all the trace steps that are relevant to termination

\*******************************************************************/

void termination_baset::find_required_steps(
  const goto_tracet &goto_trace,
  goto_tracet::stepst::const_iterator &loop_begin,
  required_stepst &required_steps,
  const std::string &prefix) const
{
  find_symbols_sett required_symbols;
  unsigned before=0, after=1;

  // initialize: find all (potential) loop exits and
  // remember the symbols in them
  for(goto_tracet::stepst::const_iterator it1=loop_begin;
      it1!=goto_trace.steps.end();
      it1++)
  {
    if(it1->pc->is_goto() &&
       it1->pc->function==loop_begin->pc->function)
    {
      bool found_next=false, found_target=false;
      goto_programt::const_targett next=it1->pc; next++;
      goto_programt::const_targett target=it1->pc->targets.front();

      for(goto_tracet::stepst::const_iterator it2=loop_begin;
          it2!=goto_trace.steps.end();
          it2++)
      {
        if(it1!=it2)
        {
          if(it2->pc==next)
            found_next=true;
          else if(it2->pc==target)
            found_target=true;
        }
      }

      if(!found_target || !found_next)
      {
        exprt temp=it1->cond_expr;
        remove_ssa_ids(temp);
        find_symbols(temp, required_symbols);
      }
    }
  }

  #if 0
  std::cout << "INITIAL SYMBOLS: ";
  for(find_symbols_sett::const_iterator it=required_symbols.begin();
      it!=required_symbols.end();
      it++)
    std::cout << *it << ", ";
  std::cout << std::endl;
  #endif

  // get the fixpoint
  while(before!=after)
  {
    before=required_symbols.size();

    for(goto_tracet::stepst::const_iterator step=loop_begin;
        step!=goto_trace.steps.end();
        step++)
    {
      find_symbols_sett intersection;

      if(step->is_assignment())
      {
        exprt lhs, rhs;

        const codet &code=to_code(step->pc->code);

        if(code.get_statement()==ID_assign)
        {
          const code_assignt &acode=to_code_assign(step->pc->code);
          lhs=acode.lhs();
          rhs=acode.rhs();
        }
        else if(code.get_statement()==ID_function_call)
        {
          const code_function_callt fcode=to_code_function_call(step->pc->code);
          lhs=fcode.lhs();
          rhs=fcode.op2();
        }
        else
          throw "Unexpected assign statement";

        if(lhs.id()==ID_symbol &&
           has_prefix(lhs.get_string(ID_identifier), prefix))
        {
          // if we depend on the RHS syms, we also need the pre-symbol
          find_symbols_sett rhs_sym;
          find_symbols(rhs, rhs_sym);

          if(intersects(rhs_sym, required_symbols))
          {
            find_symbols(lhs, required_symbols);
            required_steps.insert(&(*step));
          }
        }
        else
        {
          find_symbols_sett lhs_sym;

          if(lhs.id()==ID_index)
            find_symbols(lhs.op0(), lhs_sym); // we're not modifying the index
          else
            find_symbols(lhs, lhs_sym);

           if(intersects(lhs_sym, required_symbols))
           {
             find_symbols(rhs, required_symbols);
             required_steps.insert(&(*step));
           }
        }
      }
      else if(step->is_assume())
      {
        find_symbols_sett syms;
        find_symbols(step->pc->guard, syms);

        if(intersects(syms, required_symbols))
        {
          required_symbols.insert(syms.begin(), syms.end());
          required_steps.insert(&(*step));
        }
      }
    }

    after=required_symbols.size();

  #if 0
  std::cout << "REQUIRED SYMBOLS: ";
  for(find_symbols_sett::const_iterator it=required_symbols.begin();
      it!=required_symbols.end();
      it++)
    std::cout << *it << ", ";
  std::cout << std::endl;
  #endif
  }
}

/********************************************************************\

 Function: termination_baset::get_loop

 Inputs:

 Outputs:

 Purpose: Find a loop in the CE

\*******************************************************************/

goto_tracet::stepst::const_iterator termination_baset::get_loop(
  goto_tracet &trace)
{
  if(trace.steps.size()<3)
    throw "counterexample is too short";

  const goto_trace_stept &assertion=trace.steps.back();

  assert(assertion.is_assert());

  goto_tracet::stepst::const_iterator step=--trace.steps.end();

  // skip over assertion
  step--;

  // we need to see the copy-instruction at least once.
  assert(assertion.pc->guard.operands().size()==2);
  const irep_idt my_id=assertion.pc->guard.op0().get("identifier");
  bool seen_copy=false;

  while(step->pc!=assertion.pc || !seen_copy)
  {
    if(step==trace.steps.begin()) // failed
      throw "failed to find beginning of loop";

    if(step->pc->type==ASSIGN)
    {
      const code_assignt &code=to_code_assign(step->pc->code);
      if(code.lhs().id()=="symbol" &&
         code.lhs().get("identifier")==my_id)
        seen_copy=true;
    }

    step--;
  }

  // found it!
  return step;
}


/********************************************************************\

 Function: termination_baset::intersects()

 Inputs:

 Outputs:

 Purpose: A little helper that tells us if two sets of irep_idts intersect
          (std::intersection doesn't work because of equality operator problems)

\********************************************************************/

bool termination_baset::intersects(
  const find_symbols_sett &a,
  const find_symbols_sett &b) const
{
  for(find_symbols_sett::const_iterator it1=a.begin();
      it1!=a.end();
      it1++)
  {
    for(find_symbols_sett::const_iterator it2=b.begin();
        it2!=b.end();
        it2++)
    {
      if(*it1==*it2)
        return true;
    }
  }

  return false;
}

/********************************************************************\

 Function: termination_baset::find_next_loop

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

goto_programt::const_targett termination_baset::find_next_loop(
  goto_programt::const_targett current,
  const goto_programt &program,
  std::list<goto_programt::const_targett> &recursion_stack) const
{
  /* The program contains only termination-assertions, i.e.,
     we look only for assertions. */

  current++;

  while(current!=program.instructions.end())
  {
    switch(current->type)
    {
      case ASSERT:
          return current;
      case FUNCTION_CALL:
        {
          const code_function_callt &code=to_code_function_call(current->code);
          const irep_idt &fid=code.function().get("identifier");

          goto_functionst::function_mapt::const_iterator fit=
              goto_functions.function_map.find(fid);

          if(fit==goto_functions.function_map.end() ||
             fit->second.body.instructions.empty())
            current++; // ignore the call
          else
          {
            if(std::find(recursion_stack.begin(),
                         recursion_stack.end(),
                         current) == recursion_stack.end())
            {
              recursion_stack.push_back(current);
              current=fit->second.body.instructions.begin();
            }
            else
              current++; // no recursion necessary
          }
        }
        break;
      case END_FUNCTION:
        if(!recursion_stack.empty())
        {
          current=recursion_stack.back();
          recursion_stack.pop_back();
        }
        current++;
        break;
      default:
        current++;
    }
  }

  assert(recursion_stack.empty());

  // no more assertions
  return program.instructions.end();
}

/********************************************************************\

 Function: termination_baset::show_stats

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_baset::show_stats()
{
  std::stringstream ss;

  ss << "Statistics: " << ranksynth_calls << " ranking synthesis calls, " <<
    total_loops << " loops, " <<
    total_loops-nonterminating_loops << " loops terminate, " <<
    nonterminating_loops << " non-terminating loops.";

  status(ss.str());
  ss.str("");

  ss << "Time: " << time2string(current_time()-start_time) << " s total, " <<
    time2string(modelchecker_time) << " s model checker, " <<
    time2string(ranking_time) << " s ranking time, " <<
    time2string(counter_example_extraction_time) << " s counterexample extraction, " <<
    time2string(final_check_time) << " s final check";

  status(ss.str());
}

/********************************************************************\

 Function: termination_baset::bmc

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool termination_baset::bmc(
  concrete_modelt &model,
  fine_timet &modelchecker_time,
  fine_timet &unsafe_time,
  fine_timet &safe_time)
{
  bool res=false;

  #if 0
  std::ofstream out("model");
  model.goto_functions.output(ns, out);
  out.close();
  #endif

  fine_timet before=current_time();

  symex_target_equationt equation(ns);
  custom_symext symex(ns, shadow_context, equation);
  satcheckt satcheck;
  bv_pointerst bv_pointers(ns, satcheck);

  symex.options.set_option("assertions", true);
  satcheck.set_verbosity(2);
  satcheck.set_message_handler(get_message_handler());
  bv_pointers.set_verbosity(2);
  bv_pointers.set_message_handler(get_message_handler());

  try
  {
    symex(model.goto_functions);

    bv_pointerst::resultt satres;

    if(!symex.has_remaining_claims())
      satres=bv_pointerst::D_UNSATISFIABLE;
    else
    {
      equation.convert(bv_pointers);
      satres=bv_pointers.dec_solve();
    }
    modelchecker_time+=current_time()-before;

    switch(satres)
    {
      case bv_pointerst::D_TAUTOLOGY:
      case bv_pointerst::D_SATISFIABLE:
        unsafe_time+=current_time()-before;
        res=false;
        break;
      case bv_pointerst::D_UNSATISFIABLE:
        safe_time+=current_time()-before;
        res=true;
        break;
      default:
        throw("SAT Solver error.");
        break;
    }
  }
  catch (const std::bad_alloc &s)
  {
    status(std::string("BMC Exception: Memory exhausted"));
  }
  catch (const std::string &s)
  {
    status(std::string("BMC Exception: ") + s);
  }
  catch (const char *s)
  {
    status(std::string("BMC Exception: ") + s);
  }
  catch (unsigned u)
  {
    status(std::string("BMC Exception: ") + i2string(u));
  }

  return res;
}

/********************************************************************\

 Function: termination_baset::cegar

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool termination_baset::cegar(
  concrete_modelt &model,
  goto_tracet &goto_trace,
  fine_timet &modelchecker_time,
  fine_timet &unsafe_time,
  fine_timet &safe_time)
{
  goto_trace.clear();

  #if 0
  std::ofstream out("model");
  model.goto_functions.output(ns, out);
  out.close();
  #endif

  null_message_handlert nmh;
  message_handlert &mh = (verbosity >= 8) ? get_message_handler() : nmh;
  
  loop_componentt::argst args(mh, model);
  
  std::auto_ptr<refinert> refiner(select_refiner(options, args));
  std::auto_ptr<abstractort> abstractor(select_abstractor(options, args));
  std::auto_ptr<modelcheckert> modelchecker(select_modelchecker(options, args));
  std::auto_ptr<simulatort> simulator(select_simulator(options, args, shadow_context));

  unsigned this_verb=get_verbosity()-2;

  // set their verbosity -- all the same for now
  refiner->set_verbosity(this_verb);
  abstractor->set_verbosity(this_verb);
  modelchecker->set_verbosity(this_verb);
  simulator->set_verbosity(this_verb);

  try
  {
    satabs_safety_checker_baset safety_checker(ns, *abstractor, *refiner, *modelchecker, *simulator);
    safety_checker.set_message_handler(mh);
    safety_checker.set_verbosity(this_verb);

    fine_timet before=current_time();
    safety_checkert::resultt result=safety_checker(model.goto_functions);
    fine_timet diff=current_time()-before;
    modelchecker_time+=diff;

    switch(result)
    {
    case safety_checkert::ERROR:
      unsafe_time+=diff;
      throw "CEGAR Error";

    case safety_checkert::UNSAFE:
      goto_trace.clear();
      goto_trace.swap(safety_checker.error_trace);

      unsafe_time+=diff;
      return false; // not safe

    case safety_checkert::SAFE:
      safe_time+=diff;
      return true; // safe

    default:
      unsafe_time+=diff;
      throw std::string("CEGAR Result: ") + i2string(result);
    }
  }
  catch(const std::bad_alloc &s)
  {
    status(std::string("CEGAR Loop Exception: Memory exhausted"));
  }
  catch(const std::string &s)
  {
    status(std::string("CEGAR Loop Exception: ") + s);
  }
  catch(const char *s)
  {
    status(std::string("CEGAR Loop Exception: ") + s);
    if(std::string(s)=="refinement failure")
    {
      status("Dumping failure.o");
      write_goto_binary("failure.o", ns.get_context(), model.goto_functions, mh);
    }
  }
  catch(unsigned u)
  {
    status(std::string("CEGAR Loop Exception: ") + i2string(u));
  }
  catch(...)
  {
    status("UNKNOWN EXCEPTION CAUGHT");
  }

  return false;
}

/********************************************************************\

 Function: termination_baset::cegar

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool termination_baset::cegar(
  concrete_modelt &model,
  fine_timet &modelchecker_time,
  fine_timet &unsafe_time,
  fine_timet &safe_time)
{
  goto_tracet goto_trace;
  return cegar(model, goto_trace, modelchecker_time, unsafe_time, safe_time);
}

/********************************************************************\

 Function: termination_baset::set_options

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void termination_baset::set_options()
{
  if(cmdline.isset("refiner"))
    options.set_option("refiner", cmdline.getval("refiner"));
  else
    options.set_option("refiner", "wp");

  if(cmdline.isset("abstractor"))
    options.set_option("abstractor", cmdline.getval("abstractor"));
  else
    options.set_option("abstractor", "wp");

  if(cmdline.isset("modelchecker"))
    options.set_option("modelchecker", cmdline.getval("modelchecker"));
  else
    options.set_option("modelchecker", "boom");

  if(cmdline.isset("simulator"))
    options.set_option("simulator", cmdline.getval("simulator"));
  else
    options.set_option("simulator", "sat");
}
