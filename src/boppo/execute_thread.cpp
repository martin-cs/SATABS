/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include "simulator.h"

/*******************************************************************\

Function: simulatort::execute_thread

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::execute_thread(
  const statet &state,
  unsigned thread_nr,
  bool check_property,
  queuet &queue)
{
  #ifdef DEBUG
  std::cout << "simulatort::execute_thread1 "
            << thread
            << std::endl;
  #endif
  
  assert(thread_nr<state.data().threads.size());
  
  const statet::threadt &thread=state.data().threads[thread_nr];
            
  const program_formulat::formula_goto_programt::instructiont
    &instruction=*thread.PC;

  if(instruction.is_goto()) // special case
    compute_goto_successors(state, thread_nr, queue);
  else if(instruction.is_start_thread())
    compute_start_thread_successors(state, thread_nr, queue); // yet another special case
  else if(instruction.is_end_thread())
    compute_end_thread_successors(state, thread_nr, queue); // yet another special case
  else
  {
    statet new_state(state);
    new_state.set_previous(state, thread_nr);

    execute_instruction(new_state, thread_nr, instruction, check_property);

    // get next PC: just increment
    new_state.data_w().threads[thread_nr].PC++;
    
    queue.add(new_state);
  }
    
  #ifdef DEBUG
  std::cout << "simulatort::execute_thread2" << std::endl;
  #endif
}

/*******************************************************************\

Function: simulatort::compute_goto_successors

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::compute_goto_successors(
  const statet &state,
  unsigned thread_nr,
  queuet &queue)
{
  const instructiont &instruction=
    *state.data().threads[thread_nr].PC;

  // must have target
  assert(!instruction.targets.empty());

  formulat instantiated_guard=
    instantiate(state, thread_nr, instruction.guard);

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
    new_state.data_w().threads[thread_nr].PC++;
    new_state.data_w().guard=new_guard_not_taken;
    new_state.data_w().taken=false;
    new_state.set_previous(state, thread_nr);
    queue.add(new_state);
  }

  for(program_formulat::formula_goto_programt::
        instructiont::targetst::const_iterator
      t_it=instruction.targets.begin();
      t_it!=instruction.targets.end();
      t_it++)
  {
    statet new_state=state;
    new_state.data_w().threads[thread_nr].PC=*t_it;
    new_state.data_w().guard=new_guard_taken;
    new_state.data_w().taken=true;
    new_state.set_previous(state, thread_nr);
    queue.add(new_state);
  }
}

/*******************************************************************\

Function: simulatort::compute_start_thread_successors

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::compute_start_thread_successors(
  const statet &state,
  unsigned thread_nr,
  queuet &queue)
{
  if(mode==FULL)
  {
    if(state.data().threads.size()>10) // max to prevent diverging
      throw "thread max is reached, your code probably diverges";
    
    const instructiont &instruction=*state.data().threads[thread_nr].PC;
    
    assert(instruction.targets.size()==1);
    
    statet new_state=state;

    instructiont::const_targett next_PC=
      instruction.targets.front();

    new_state.data_w().threads.push_back(statet::threadt());
    statet::threadt &new_thread=new_state.data_w().threads.back();
    new_thread.PC=next_PC;
    new_thread.program=new_state.data().threads[thread_nr].program;

    // copy locals
    new_thread.locals=new_state.data_w().threads[thread_nr].locals;

    new_state.data_w().threads[thread_nr].PC++;
    new_state.set_previous(state, thread_nr);  
    
    queue.add(new_state);
  }
  else if(mode==TVS)
  {
    throw "TVS";
  }
  else
    assert(false);
}

/*******************************************************************\

Function: simulatort::compute_end_thread_successors

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::compute_end_thread_successors(
  const statet &state,
  unsigned thread,
  queuet &queue)
{
  // equivalent to jumping to the "end"
  statet new_state=state;
  new_state.set_previous(state, thread);

  new_state.data_w().threads[thread].PC=
    new_state.data_w().threads[thread].end_pc();
  
  queue.add(new_state);
}

/*******************************************************************\

Function: simulatort::execute_instruction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::execute_instruction(
  statet &state,
  unsigned thread_nr,
  const program_formulat::formula_goto_programt::instructiont &instruction,
  bool check_property)
{
  #ifdef DEBUG
  std::cout << "simulatort::execute_instruction1"
            << std::endl;
  #endif

  switch(instruction.type)
  {
  case GOTO:
    // do nothing
    break;

  case ASSUME:
    execute_assume(state, thread_nr, instruction);
    break;

  case ASSERT:
    if(check_property)
      execute_assert(state, thread_nr, instruction);
    break;

  case ASSIGN:
    execute_assign(state, thread_nr, instruction);
    break;

  case OTHER:
    assert(false);
    break;

  case FUNCTION_CALL:
    assert(false);
    break;

  case SKIP:
  case LOCATION:
  case END_FUNCTION:
    // do nothing
    break;
    
  case START_THREAD:
    break;
    
  case END_THREAD:
    break;
    
  case ATOMIC_BEGIN:
    state.data_w().in_atomic_section=true;
    break;
    
  case ATOMIC_END:
    state.data_w().in_atomic_section=false;
    break;

  case DECL:    
  case DEAD:
    break;
    
  case THROW:
  case CATCH:
    assert(false);
    
  default:
    std::cerr << instruction.type << std::endl;
    assert(false);  
  }

  #ifdef DEBUG
  std::cout << "simulatort::execute_instruction2" << std::endl;
  #endif
}

/*******************************************************************\

Function: simulatort::execute_assume

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::execute_assume(
  statet &state,
  unsigned thread_nr,
  const program_formulat::formula_goto_programt::instructiont &instruction)
{
  formulat condition=
    instantiate(state, thread_nr, instruction.guard);
    
  if(condition.is_true()) return;

  // just add it to the guard
  state.data_w().guard=
    formula_container.gen_and(state.data().guard, condition);
}

/*******************************************************************\

Function: simulatort::execute_assert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::execute_assert(
  statet &state,
  unsigned thread_nr,
  const program_formulat::formula_goto_programt::instructiont &instruction)
{
  #ifdef DEBUG
  std::cout << "simulatort::execute_assert1\n";
  #endif
  
  formulat condition=
    instantiate(state, thread_nr, instruction.guard);
    
  #ifdef DEBUG
  std::cout << "simulatort::execute_assert2\n";
  #endif
  
  formulat property=
    formula_container.gen_and(
      state.data_w().guard,
      formula_container.gen_not(condition));

  #ifdef DEBUG
  std::cout << "simulatort::execute_assert3\n";
  #endif
  
  // see if it is reachable
  if(!property.is_false() &&
     is_satisfiable(property))
  {
    tracet trace;

    compute_trace(state, trace, true);
    
    if(loops)
      loop_detection(trace);

    dump_trace(trace, instruction);

    std::cout << "Assertion violated" << std::endl;
    std::cout << std::endl;

    error_state_found=true;
  }

  #ifdef DEBUG
  std::cout << "simulatort::execute_assert4\n";
  #endif
}

/*******************************************************************\

Function: simulatort::execute_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::execute_assign(
  statet &state,
  unsigned thread_nr,
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
        thread_nr,
        instantiate(state, thread_nr, it->value));
    }
  
  // do constraint
  formulat instantiated_constraint=
    instantiate(
      state,
      new_state,
      thread_nr,
      instruction.code.constraint);

  new_state.data_w().guard=
    formula_container.gen_and(
      state.data().guard,
      instantiated_constraint);
  
  state.swap(new_state);
}

/*******************************************************************\

Function: simulatort::execute_synchronize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulatort::execute_synchronize(
  statet &state,
  unsigned thread_nr,
  const program_formulat::formula_goto_programt::instructiont &instruction)
{
  
}
