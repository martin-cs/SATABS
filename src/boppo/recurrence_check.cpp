/*******************************************************************\

Module: Symbolic Simulator for Boolean Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <solvers/sat/satcheck.h>
#include <solvers/qbf/qbf_quantor.h>
#include <solvers/qbf/qbf_skizzo.h>

#include "simulator_ct.h"
#include "qbf_cache.h"

extern qbf_cachet qbf_cache;

/*******************************************************************\

Function: simulator_ctt::is_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_ctt::is_equal(propt &prop, bvt &or_bv, formulat f1, formulat f2)
{
  literalt l1=f1.convert(prop);
  literalt l2=f2.convert(prop);

  if(l1==l2) // this won't be different, ever
    return;

  or_bv.push_back(prop.lxor(l1, l2));
}

/*******************************************************************\

Function: simulator_ctt::is_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simulator_ctt::is_equal(propt &prop, statet &s1, statet &s2)
{
  assert(s1.data().threads.front().PC==
         s2.data().threads.front().PC);
  
  bvt or_bv;

  assert(s1.data().globals.size()==
         s2.data().globals.size());

  for(unsigned i=0; i<s1.data().globals.size(); i++)
  {
    formulat f1=s1.data().globals[i];
    formulat f2=s2.data().globals[i];
    is_equal(prop, or_bv, f1, f2);
  }
  
  assert(s1.data().threads.front().locals.size()==
         s2.data().threads.front().locals.size());

  for(unsigned i=0; i<s1.data().threads.front().locals.size(); i++)
  {
    formulat f1=s1.data().threads.front().locals[i];
    formulat f2=s2.data().threads.front().locals[i];
    is_equal(prop, or_bv, f1, f2);
  }
  
  // these are equal!
  if(or_bv.empty()) return true;
  
  prop.lcnf(or_bv);
  
  // don't know
  return false;
}

/*******************************************************************\

Function: simulator_ctt::has_recurrence

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simulator_ctt::has_recurrence(const statet &state)
{
  assert(!state.data().threads.front().is_at_end());
  
  // get the PC we care about
  const_targett PC=state.data().threads.front().PC;

  locationst locations_rev;

  {
    statet s=state;
    while(true)
    {
      if(PC==s.data().threads.front().PC)
        locations_rev.push_back(s);
      if(s.data().is_initial_state) break;
      s=s.data().previous;
    }
  }
  
  // we reverse this to get a path
  locationst locations;
  locations.reserve(locations_rev.size());
  
  for(locationst::const_reverse_iterator
      it=locations_rev.rbegin();
      it!=(locationst::const_reverse_iterator)locations_rev.rend();
      it++)
    locations.push_back(*it);

  // we must have at least one
  assert(locations.size()>=1);
  
  if(locations.size()<2) return false;

  std::cout << "Depth: " << locations.size()-1 << std::endl;

  return has_recurrence_qbf(locations);  
  //return has_recurrence_sat(locations);  
}

/*******************************************************************\

Function: simulator_ctt::has_recurrence_sat

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simulator_ctt::has_recurrence_sat(locationst &locations)
{
  const statet &state=locations.back();

  // reset all formulas
  formula_container.reset_prop();

  // use SAT -- recurrence diamater

  satcheckt prop;
  
  // the guard must be true
  
  prop.l_set_to(state.data().guard.convert(prop), true);
  
  // build pair-wise comparisons
  for(unsigned a=0; a<locations.size(); a++)
    for(unsigned b=a+1; b<locations.size(); b++)
      if(is_equal(prop, locations[a], locations[b]))
        return true;

  bool is_sat=is_satisfiable(prop);
  
  if(is_sat) std::cout << "SAT"; else std::cout << "UNSAT";
  std::cout << std::endl;

  return !is_sat;
}

/*******************************************************************\

Function: simulator_ctt::has_recurrence_qbf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simulator_ctt::has_recurrence_qbf(locationst &locations)
{
  std::cout << "Building formula" << std::endl;

  const statet &state=locations.back();
  const state_dt &state_d=state.data();

  // we do the conversion separately, as we need
  // different non-deterministic choices for both

  // PART 1
  // reset all formulas
  formula_container.reset_prop();

  //qbf_quantort solver;
  qbf_skizzot solver;
  
  // first do the conversion for the last location

  literalt x_guard_literal=state_d.guard.convert(solver);

  // do the variables of the state
  bvt x_variables;
  
  const std::set<unsigned> &vars=state_d.threads.front().PC->code.alive;
  x_variables.reserve(vars.size());
  
  std::cout << "X:  ";
  
  for(std::set<unsigned>::const_iterator it=vars.begin();
      it!=vars.end();
      it++)
  {
    formulat f=state_d.get_var(*it, 0);
    x_variables.push_back(f.convert(solver));
    std::cout << " " << (f.is_true()?'T':f.is_false()?'F':'?');
  }
  
  std::cout << std::endl;

  typedef std::set<literalt> state_inputst;
  state_inputst x_inputs;
  formula_container.get_nondet_literals(x_inputs);

  // PART 2 -- locations 0,...,n-1
  // FORALL x in state EXISTS y in entry
  // guard(x) => (\/y guard(y) AND values(x)=values(y))

  // reset all formulas
  formula_container.reset_prop();

  // do the conversion for y
  bvt clause;

  clause.push_back(solver.lnot(x_guard_literal));

  for(unsigned i=0; i<locations.size()-1; i++)
  {
    statet &y=locations[i];
  
    literalt y_guard_literal=y.data().guard.convert(solver);

    bvt y_variables;
    y_variables.reserve(vars.size());
    
    std::cout << "Y" << i << ": ";

    for(std::set<unsigned>::const_iterator it=vars.begin();
        it!=vars.end();
        it++)
    {
      formulat f=y.data().get_var(*it, 0);
      y_variables.push_back(f.convert(solver));
      std::cout << " " << (f.is_true()?'T':f.is_false()?'F':'?');
    }
    
    std::cout << std::endl;
  
    // build values(x)=values(y)
    bvt eq_bv;
    eq_bv.reserve(vars.size()+1);
  
    for(unsigned i=0; i<y_variables.size(); i++)
      eq_bv.push_back(solver.lequal(x_variables[i], y_variables[i]));

    eq_bv.push_back(y_guard_literal);

    clause.push_back(solver.land(eq_bv));
  }

  solver.lcnf(clause);

  // build quantifiers
  
  for(state_inputst::const_iterator it=x_inputs.begin();
      it!=x_inputs.end(); it++)
    solver.add_quantifier(qdimacs_cnft::quantifiert::UNIVERSAL, *it);

  // all the rest are existential

  for(unsigned i=1; i<solver.no_variables(); i++)
  {
    literalt l;
    l.set(i, false);

    if(x_inputs.find(l)==x_inputs.end())
      solver.add_quantifier(qdimacs_cnft::quantifiert::EXISTENTIAL, l);
  }
  
  std::cout << "Running " << solver.solver_text() << ", "
            << solver.no_variables() << " variables, "
            << solver.no_clauses() << " clauses"
            << std::endl;
            
  bool result;

  switch(solver.prop_solve())
  {
  case propt::P_UNSATISFIABLE: // this is false
    result=false;
    break;
  
  case propt::P_SATISFIABLE: // this is true
    result=true;
    break;
    
  default:
    throw "Error from "+solver.solver_text();
  }
  
  if(result)
    std::cout << "Recurrence found" << std::endl;
  else
    std::cout << "No recurrence found" << std::endl;

  return result;
}

