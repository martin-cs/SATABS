/*******************************************************************\
  
Module: Predicate Refinement for CEGAR

Author: Daniel Kroening

Date: June 2003
 
\*******************************************************************/

#include "refiner.h"
#include "../abstractor/discover_predicates.h"
#include "../abstractor/check_redundancy.h"

static bool is_pointer_predicate(const exprt& p)
{
  return p.id()==ID_equal &&
         (p.op0().id()==ID_address_of || p.op1().id()==ID_address_of);
}

/*******************************************************************\

Function: refinert::add_predicates

  Inputs: max_predicates_to_add specifies the maximum number of
          of new predicates that should be added.  If this is set
          to a negative value, then there is no limit

 Outputs: returns the number of predicates that were added

 Purpose: generate a new set of predicates given an expressions

\*******************************************************************/

void refinert::add_predicates(
  abstract_programt::targett pc,
  predicatest &predicates,
  const exprt &expr,
  bool &found_new,
  wheret where)
{

  std::set<predicatet> new_predicates;
  discover_predicates(expr, new_predicates, concrete_model.ns, no_mixed_predicates);
  
  std::set<unsigned> new_predicates_no;

  if(prefer_non_pointer_predicates)
  {
	  // first, look for predicates that do not involve address-of
	  for(std::set<predicatet>::const_iterator
			  p_it=new_predicates.begin();
			  p_it!=new_predicates.end() && (num_predicates_added < max_predicates_to_add);
			  p_it++)
	  {
		  const exprt &p=*p_it;

		  std::cout << "Considering " << from_expr(concrete_model.ns, "", p) << "\n";

		  if(is_pointer_predicate(p))
		  {
			  std::cout << "It is a pointer pred\n";
		  } else
		  {
			  std::cout << "It is not a pointer pred\n";
		  }

		  if(is_pointer_predicate(p) || is_redundant(p, concrete_model.ns))
		  {
			  // Do not add redundant predicate, or predicate which involves address-of
			  continue;
		  }

		  if(!predicates.find(p))
		  {
			  std::string msg="Adding predicate `"+from_expr(concrete_model.ns, "", p)+"'";
			  debug(msg);
			  debug(p.pretty());
			  num_predicates_added++;
		  }

		  new_predicates_no.insert(predicates.lookup(*p_it));
	  }
  }

  // we just take them all
  for(std::set<predicatet>::const_iterator
      p_it=new_predicates.begin();
      p_it!=new_predicates.end() && (num_predicates_added < max_predicates_to_add);
      p_it++)
  {
    const exprt &p=*p_it;

    if(is_redundant(p, concrete_model.ns))
    {
    	// Do not add redundant predicate
    	continue;
    }

    if(!predicates.find(p))
    {
      std::string msg="Adding predicate `"+from_expr(concrete_model.ns, "", p)+"'";
      debug(msg);
      debug(p.pretty());
      num_predicates_added++;
    }

    new_predicates_no.insert(predicates.lookup(*p_it));

  }
    
  std::set<unsigned> &trans_predicates=
    where==FROM?
      pc->code.get_transition_relation().from_predicates:
      pc->code.get_transition_relation().to_predicates;

  unsigned old=trans_predicates.size();

  for(std::set<unsigned>::const_iterator
      p_it=new_predicates_no.begin();
      p_it!=new_predicates_no.end();
      p_it++)
    trans_predicates.insert(*p_it);

  if(trans_predicates.size()>old)
  {
    found_new=true;
    pc->code.re_abstract=true;
  }

}

