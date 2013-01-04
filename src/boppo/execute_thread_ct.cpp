/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include "simulator_ct.h"

/*******************************************************************\

Function: simulator_ctt::compute_goto_successors

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_ctt::compute_goto_successors(
  const statet &state,
  queuet &queue)
{
  const instructiont &instruction=*state.data().threads.front().PC;
  unsigned count=0;

  // must have target
  assert(!instruction.targets.empty());

  formulat instantiated_guard=
    instantiate(state, 0, instruction.guard);

  formulat new_guard_taken;

  if(instantiated_guard.is_true())
    new_guard_taken=state.data().guard;
  else
  {
    new_guard_taken=formula_container.gen_and(
      instantiated_guard,
      state.data().guard);

    formulat new_guard_not_taken=formula_container.gen_and(
      formula_container.gen_not(instantiated_guard),
      state.data().guard);

    // do "guard is false" case

    statet new_state=state;
    new_state.data_w().threads.front().PC++;
    new_state.data_w().guard=new_guard_not_taken;
    new_state.data_w().taken=false;
    new_state.set_previous(state, 0);
    queue.add(new_state);

    count++;
  }

  for(program_formulat::formula_goto_programt::
        instructiont::targetst::const_iterator
      t_it=instruction.targets.begin();
      t_it!=instruction.targets.end();
      t_it++)
  {
    statet new_state=state;
    new_state.data_w().threads.front().PC=*t_it;
    new_state.data_w().guard=new_guard_taken;
    new_state.data_w().taken=true;
    new_state.set_previous(state, 0);
    queue.add(new_state);

    count++;
  }
  
  if(count>=2) path_counter+=count-1;
}

/*******************************************************************\

Function: simulator_ctt::execute_instruction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_ctt::execute_instruction(
  statet &state,
  const program_formulat::formula_goto_programt::instructiont &instruction)
{
  switch(instruction.type)
  {
  case GOTO:
    assert(false);
    // done somewhere else
    break;

  case ASSUME:
    execute_assume(state, instruction);
    break;

  case ASSERT:
    execute_assert(state, instruction);
    break;

  case ASSIGN:
    execute_assign(state, instruction);
    break;
    
  case FUNCTION_CALL:
    assert(false); // done somewhere else
    break;

  case OTHER:
    assert(false);
    break;

  case SKIP:
  case LOCATION:
  case END_FUNCTION:
    // do nothing
    break;
    
  case START_THREAD:
    throw "start_thread is not supported";
    break;
    
  case END_THREAD:
    assert(false);
    break;
    
  case ATOMIC_BEGIN:
    state.data_w().in_atomic_section=true;
    break;
    
  case ATOMIC_END:
    state.data_w().in_atomic_section=false;
    break;
    
  case DEAD:
    break;
    
  case RETURN:
    assert(false); // done somewhere else
    break;
    
  default:
    std::cerr << instruction.type << std::endl;
    assert(false);  
  }
}

/*******************************************************************\

Function: simulator_ctt::execute_assume

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_ctt::execute_assume(
  statet &state,
  const program_formulat::formula_goto_programt::instructiont &instruction)
{
  formulat condition=
    instantiate(state, 0, instruction.guard);
    
  if(condition.is_true()) return;

  // just add it to the guard
  state.data_w().guard=
    formula_container.gen_and(state.data_w().guard, condition);
}

/*******************************************************************\

Function: simulator_ctt::execute_assert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_ctt::execute_assert(
  statet &state,
  const program_formulat::formula_goto_programt::instructiont &instruction)
{
  std::cout << "CHECKING ASSERTION\n";

  formulat condition=
    instantiate(state, 0, instruction.guard);
    
  formulat property=
    formula_container.gen_and(
      state.data().guard,
      formula_container.gen_not(condition));

  // see if it is reachable
  if(!property.is_false() &&
     is_satisfiable(property))
  {
    tracet trace;

    compute_trace(state, trace, true);
    dump_trace(trace, instruction);
    std::cout << "Assertion violated" << std::endl;
    std::cout << std::endl;

    error_state_found=true;
  }
  
  #if 0
  else
  {
    // otherwise, treat this like an assumption
    state.data_w().guard=
      formula_container.gen_and(state.data().guard, condition);
  }
  #endif
}

/*******************************************************************\

Function: simulator_ctt::execute_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_ctt::execute_assign(
  statet &state,
  const program_formulat::formula_goto_programt::instructiont &instruction)
{
  statet new_state(state);
  
  new_state.detatch();

  for(program_formulat::assignst::const_iterator
      it=instruction.code.assigns.begin();
      it!=instruction.code.assigns.end();
      it++)
    if(it->in_use)
    {
      assert(it->variable<program_formula.variables.size());

      new_state.data_w().set_var(
        it->variable,
        0,
        instantiate(state, 0, it->value));
    }
  
  // do constraint
  formulat instantiated_constraint=
    instantiate(
      state,
      new_state,
      0,
      instruction.code.constraint);

  new_state.data_w().guard=
    formula_container.gen_and(
      state.data_w().guard,
      instantiated_constraint);
  
  state.swap(new_state);
}

/*******************************************************************\

Function: simulator_ctt::execute_functioncall

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_ctt::execute_functioncall(
  const statet &state,
  edget &edge)
{
  const program_formulat::formula_goto_programt::instructiont
    &instruction=*state.data().threads.front().PC;
  const irep_idt &function_id=instruction.code.function;
  
  // find in program formula
  program_formulat::function_mapt::const_iterator
    f_it=program_formula.function_map.find(function_id);

  assert(f_it!=program_formula.function_map.end());
  
  const program_formulat::functiont &f=f_it->second;

  // produce a start state
  
  statet start_state(state);
  statet::threadt &thread=start_state.data_w().threads.back();
  
  // adjust PC
  thread.program=&(f.body);
  thread.PC=thread.start_pc();
  
  // assign args
  assert(instruction.code.function_args.size()==f.args.size());
  
  for(unsigned i=0; i<f.args.size(); i++)
  {
    formulat formula=instruction.code.function_args[i];
    formula=instantiate(state, 0, formula);
    start_state.data_w().set_var(f.args[i], 0, formula);
  }

  std::cout << "Adding edge for " << function_id << std::endl;
  
  // add edge
  edget &f_edge=new_edge(function_id, start_state);
  
  f_edge.calls.push_back(conft(edge, state));
}

/*******************************************************************\

Function: simulator_ctt::execute_return

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_ctt::execute_return(const statet &state, edget &edge)
{
  // compute vector of return values
  std::vector<formulat> return_values;
  
  bool have_return=!state.data().threads.front().is_at_end();

  if(have_return)
  {
    const program_formulat::formula_goto_programt::instructiont
      &return_instruction=*state.data().threads.front().PC;
    
    return_values.resize(return_instruction.code.assigns.size());

    for(unsigned i=0; i<return_values.size(); i++)
    {
      formulat f1=return_instruction.code.assigns[i].value;
      formulat f2=instantiate(state, 0, f1);
      return_values[i]=f2;
    }
  }

  // propagate to all call sites
  for(callst::const_iterator it=edge.calls.begin();
      it!=edge.calls.end();
      it++)
  {
    const conft &conf=*it;

    // save PC
    const_targett PC=conf.state.data().threads.front().PC;

    const program_formulat::formula_goto_programt::instructiont
      &call_instruction=*PC;

    // get return PC
    PC++;

    statet new_state=state;
    
    // set PC to return location
    new_state.data_w().threads.front().PC=PC;
    new_state.data_w().threads.front().program=
      conf.state.data().threads.front().program;

    if(!call_instruction.code.function_lhs.empty())
    {
      if(have_return)
      {
        assert(call_instruction.code.function_lhs.size()==
               return_values.size());
        
        // do return value
        for(unsigned i=0; i<return_values.size(); i++)
        {
          if(call_instruction.code.function_lhs[i].in_use)
          {
            unsigned lhs=call_instruction.code.function_lhs[i].variable;
            new_state.data_w().set_var(lhs, 0, return_values[i]);
          }
        }
      }
    }
    
    std::cout << "Adding to queue of " << conf.edge->function << std::endl;
    
    // put it into the right queue
    conf.edge->queue.add(new_state);
    
    // make sure this is noticed
    active_edges.insert(conf.edge);
  }
}
