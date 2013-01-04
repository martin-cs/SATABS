/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include "history.h"
#include "compare_states.h"

#define rotate(x) (((x)<<1)|((x)>>31))

//#define DEBUG

/*******************************************************************\

Function: historyt::key_hash::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

size_t historyt::key_hash::operator()(const keyt &key) const
{
  size_t result=key.PCs.size();
  
  for(PCst::const_iterator pc_it=key.PCs.begin();
      pc_it!=key.PCs.end();
      pc_it++)
    result=rotate(result)^(size_t)&(**pc_it);

  return result;
}

/*******************************************************************\

Function: historyt::small_history

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool historyt::small_history(
  const statet &state,
  bool enable_small_history)
{
  // do a cheap one in any case

  if(state.data().is_initial_state) return true;
  
  // get instruction that produced this
  const program_formulat::formula_goto_programt::instructiont
    &instruction=*state.data().previous_PC;

  if(instruction.is_skip() ||
     instruction.is_assume() ||
     instruction.is_assert())
    return false;

  if(!enable_small_history) return true;
    
  // is it cycle forming?
  if(instruction.code.can_form_cycle) return true;
  
  std::cout << "No cycle check because of small history" << std::endl;
  
  return false;
}

/*******************************************************************\

Function: historyt::check_history

  Inputs:

 Outputs: return true iff state has been there before

 Purpose:

\*******************************************************************/

bool historyt::check_history(
  const statet &state,
  bool use_cache,
  bool enable_small_history)
{
  keyt key;
  key.from_state(state);
  
  const statet new_entry(state);
  
  entry_listt empty_entry_list;
  
  std::pair<history_mapt::iterator, bool> result=
    history_map.insert(std::pair<keyt, entry_listt>(key, empty_entry_list));

  entry_listt &entry_list=result.first->second;

  if(result.second)
  {
    // actually inserted, i.e., not found
    entry_list.push_back(new_entry);
    return false;
  }
  
  std::cout << "LIST SIZE: " << entry_list.size() << std::endl;

  #if 0
  // show the list
  for(entry_listt::const_iterator
      it=entry_list.begin();
      it!=entry_list.end();
      it++)
  {
    std::cout << "L: " << it->guard;

    #if 1
    for(unsigned v=0; v<program_formula.variables.size(); v++)
    {
      std::cout << " " << it->values[v];
    }
    std::cout << std::endl;
    #endif
    
  }
  #endif
  
  // from here on, it gets expensive -- consider small history
  if(!small_history(state, enable_small_history))
    return false; // let's just assume it's new
    
  // found, do comparisons
  for(entry_listt::const_iterator
      it=entry_list.begin();
      it!=entry_list.end();
      it++)
  {
    const statet &old_entry=*it;
    
    if(compare_history(state, old_entry, use_cache))
    {
      #ifdef DEBUG
      std::cout << "MATCH!" << std::endl;
      #endif
      return true; // found match!
    }
  }

  #ifdef DEBUG  
  std::cout << "NOT FOUND\n";
  #endif
  
  // not found, insert
  entry_list.push_back(new_entry);

  // it should compare to itself
  
  assert(compare_history(state, entry_list.back(), use_cache));
  
  return false;
}

/*******************************************************************\

Function: operator==

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator==(const historyt::keyt &a,
                const historyt::keyt &b)
{
  return a.PCs==b.PCs;
}

/*******************************************************************\

Function: historyt::compare_history

  Inputs:

 Outputs: return true iff state is subsumed

 Purpose:

\*******************************************************************/

bool historyt::compare_history(
  const statet &state,
  const statet &entry,
  bool use_cache)
{
  if(state.data().guard.is_false())
    return true;

  #ifdef DEBUG
  std::cout << "historyt::compare_history1\n";
  #endif

  typedef std::set<vart> varst;
  varst vars;
  
  assert(!state.data().threads.empty());
  
  // see what variables we need to compare
  
  unsigned no_globals=state.data().globals.size();
  assert(entry.data().globals.size()==no_globals);
  
  for(unsigned v=0; v<no_globals; v++)
  {
    // don't compare dead variables
    if(!alive(program_formula, state, v, 0))
      continue;

    formulat state_f=state.data().globals[v];
    formulat entry_f=entry.data().globals[v];

    // don't compare identical, constant variables
    if(state_f.is_constant() &&
       entry_f.is_constant())
    {
      if(entry_f.id()==state_f.id())
        continue;
      else
        return false; // different constants
    }
      
    // we need to compare...
    vars.insert(vart(v));
    
    #ifdef DEBUG
    std::cout << "COMPARE: " << v << std::endl;
    #endif
  }

  for(unsigned t=0; t<state.data().threads.size(); t++)  
    for(unsigned v=0; v<state.data().threads[t].locals.size(); v++)
    {
      unsigned v2=no_globals+v;
    
      // don't compare dead variables
      if(!alive(program_formula, state, v2, t))
        continue;

      formulat state_f=state.data().threads[t].locals[v];
      formulat entry_f=entry.data().threads[t].locals[v];

      // don't compare identical, constant variables
      if(state_f.is_constant() &&
         entry_f.is_constant())
      {
        if(entry_f.id()==state_f.id())
          continue;
        else
          return false; // different constants
      }
        
      // we need to compare...
      vars.insert(vart(v2, t));
      
      #ifdef DEBUG
      std::cout << "COMPARE: " << v2 << "@" << t << std::endl;
      #endif
    }
    
  #ifdef DEBUG
  std::cout << "historyt::compare_history2\n";
  #endif
  
  if(vars.empty() &&
     entry.data().guard.is_true())
    return true;

  #ifdef DEBUG
  std::cout << "historyt::compare_history3\n";
  #endif

  if(compare_states(formula_container, state, entry, vars, use_cache))
    return true;

  return false;
}
