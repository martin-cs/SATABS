/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BOPPO_SIMULATOR_CT_H
#define CPROVER_BOPPO_SIMULATOR_CT_H

#include <hash_cont.h>

#include "simulator_base.h"
//#include "trace.h"

class simulator_ctt:public simulator_baset
{
public:
  simulator_ctt(program_formulat &_program_formula):
    simulator_baset(_program_formula)
  {
  }
  
  virtual ~simulator_ctt()
  {
  }
  
  void simulator();
  
  class queuet
  {
  public:
    queuet(formula_containert &_formula_container):
      formula_container(_formula_container)
    {
    }
  
    void add(const statet &state);

    statet next()
    {
      mapt::iterator it=map.begin();
    
      statet state=it->second;
      map.erase(it);
      return state;
    }
  
    bool empty() const
    {
      return map.empty();
    }
    
    struct keyt
    {
      unsigned priority, ordering;
      
      keyt(unsigned _priority, unsigned _ordering):
        priority(_priority),
        ordering(_ordering)
      {
      }
    };

  protected:
    formula_containert &formula_container;
    typedef std::map<keyt, statet> mapt;
    mapt map;
    
    static unsigned priority(const statet &state);
    
    friend bool operator < (const keyt &a, const keyt &b);
  };
  
protected:
  class edget;
  
  class conft
  {
  public:
    class edget *edge;
    statet state;
    
    conft(class edget &_edge, const statet &_state):edge(&_edge), state(_state)
    {
    }
  };

  typedef std::vector<conft> callst;
  
  class edget
  {
  public:
    statet in;

    callst calls;
    
    edget(formula_containert &_formula_container):
      queue(_formula_container)
    {
    }
    
    queuet queue;
    
    irep_idt function;
  };

  typedef std::list<edget> edgest;
  edgest edges;
  
  typedef edget *edge_ptrt;

  typedef std::vector<edge_ptrt> edge_ptrst;

  typedef std::map<irep_idt, edge_ptrst> summariest;
  summariest summaries;

  typedef std::set<edge_ptrt> edge_sett;
  edge_sett active_edges;

  edget &new_edge(const irep_idt &function, const statet &state)
  {
    edges.push_back(edget(formula_container));
    edget &edge=edges.back();
    edge.in=state;
    edge.function=function;
    //edge.out=make_exit_state(function);
    edge.queue.add(state);
    summaries[function].push_back(&edge);
    active_edges.insert(&edge);
    return edge;
  }
  
  void explore(const statet &state, edget &edge);

  void compute_successor_states(const statet &state, edget &edge);

  void compute_goto_successors(const statet &state, queuet &queue);

  void execute_instruction(
    statet &state,
    const program_formulat::formula_goto_programt::instructiont &instruction);

  void execute_assume(
    statet &state,
    const program_formulat::formula_goto_programt::instructiont &instruction);

  void execute_assert(
    statet &state,
    const program_formulat::formula_goto_programt::instructiont &instruction);

  void execute_assign(
    statet &state,
    const program_formulat::formula_goto_programt::instructiont &instruction);

  void execute_functioncall(
    const statet &state,
    edget &edge);

  void execute_return(
    const statet &state,
    edget &edge);

  typedef std::vector<statet> locationst;

  bool has_recurrence(const statet &state);
  bool has_recurrence_sat(locationst &locations);
  bool has_recurrence_qbf(locationst &locations);
  void is_equal(propt &prop, bvt &or_bv, formulat f1, formulat f2);
  bool is_equal(propt &prop, statet &s1, statet &s2);
  
  void summarize();
    
  statet make_exit_state(const irep_idt &function);

  // statistics
  unsigned path_counter, state_counter;
};

#endif
