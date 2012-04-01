/*******************************************************************\

Module: Predicate Refinement for CEGAR

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#include <sstream>

#include "refiner.h"
#include "../abstractor/discover_predicates.h"
#include "../abstractor/check_redundancy.h"
#include "../prepare/concrete_model.h"

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

      std::ostringstream os;
      os << "Considering " << from_expr(concrete_model.ns, "", p) << "\n";

      if(is_pointer_predicate(p))
      {
        os << "It is a pointer pred\n";
      } else
      {
        os << "It is not a pointer pred\n";
      }
      debug(os.str());

      if(!predicates.find(p))
        continue;

      if(is_pointer_predicate(p) || is_redundant(p, concrete_model.ns))
      {
        // Do not add redundant predicate, or predicate which involves address-of
        continue;
      }

      if (remove_equivalent_predicates)
      {
        //check if the predicate to be added is equivalent to some other
        //predicate which was considered already, if yes, skip it.
        bool is_eq_to_added = false;
        for(std::set<predicatet>::const_iterator
            p_added_it=new_predicates.begin();
            p_added_it!=p_it;
            p_added_it++)
        {
          const exprt &p_added = *p_added_it;
          if (is_equivalent(p,p_added,concrete_model.ns))
          {
            is_eq_to_added = true;
            std::string msg="Predicate `" + from_expr(concrete_model.ns, "", p) +
              "' is equivalent to `" + from_expr(concrete_model.ns, "", p_added) +
              "' which will was already considered, hence I am skipping it";
            debug(msg);
            debug(p.pretty());
            break;
          }
        }

        if (is_eq_to_added)
          continue;

        //check if the predicate to be added is equivalent to some
        //predicate that was added during previous cegar loops.
        bool is_eq_to_old = false;
        for(unsigned i = 0; i < predicates.size(); i++)
        {
          const exprt &p_old=predicates[i];
          if (is_equivalent(p,p_old,concrete_model.ns))
          {
            is_eq_to_old = true;
            std::string msg="Predicate `" + from_expr(concrete_model.ns, "", p) +
              "' is equivalent to `" + from_expr(concrete_model.ns, "", p_old) +
              "' which is already added, hence I am skipping it";
            debug(msg);
            debug(p.pretty());
            break;
          }
        }

        if (is_eq_to_old)
          continue;
      }

      std::string msg="Adding predicate `"+from_expr(concrete_model.ns, "", p)+"'";
      debug(msg);
      debug(p.pretty());
      num_predicates_added++;

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

    //do not add predicates that were added in previous iterations
    if(predicates.find(p))
    {
      continue;
    }

    if(is_redundant(p, concrete_model.ns))
    {
      // Do not add redundant predicate
      continue;
    }

    if (remove_equivalent_predicates)
    {
      //check if the predicate to be added is equivalent to some other
      //predicate which was considered already, if yes, skip it.
      bool is_eq_to_added = false;
      for(std::set<predicatet>::const_iterator
          p_added_it=new_predicates.begin();
          p_added_it!=p_it;
          p_added_it++)
      {
        const exprt &p_added = *p_added_it;
        if (is_equivalent(p,p_added,concrete_model.ns))
        {
          is_eq_to_added = true;
          std::string msg="Predicate `" + from_expr(concrete_model.ns, "", p) +
            "' is equivalent to `" + from_expr(concrete_model.ns, "", p_added) +
            "' which will was already considered, hence I am skipping it";
          debug(msg);
          debug(p.pretty());
          break;
        }
      }

      if (is_eq_to_added)
        continue;

      //check if the predicate to be added is equivalent to some
      //predicate that was added during previous cegar loops.
      bool is_eq_to_old = false;
      for(unsigned i = 0; i < predicates.size(); i++)
      {
        const exprt &p_old=predicates[i];
        if (is_equivalent(p,p_old,concrete_model.ns))
        {
          is_eq_to_old = true;
          std::string msg="Predicate `" + from_expr(concrete_model.ns, "", p) +
            "' is equivalent to `" + from_expr(concrete_model.ns, "", p_old) +
            "' which is already added, hence I am skipping it";
          debug(msg);
          debug(p.pretty());
          break;
        }
      }

      if (is_eq_to_old)
        continue;
    }

    std::string msg="Adding predicate `"+from_expr(concrete_model.ns, "", p)+"'";
    debug(msg);
    debug(p.pretty());
    num_predicates_added++;

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

