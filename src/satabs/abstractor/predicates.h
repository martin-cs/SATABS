/*******************************************************************\

Module: Predicate Manager

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGAR_PREDICATES_H
#define CPROVER_CEGAR_PREDICATES_H

#include <map>
#include <vector>

#include <expr.h>

typedef exprt predicatet;

class namespacet;

class predicatest
{
  public:
    // find (and add, if not found) a predicate
    unsigned lookup(const predicatet &predicate);

    // just find (and do not add, if not found) a predicate
    // true = predicate found
    bool find(const predicatet &predicate) const
    {
      return predicate_map.find(predicate)!=predicate_map.end();
    }

    // just find (and do not add, if not found) a predicate
    // true = predicate found
    bool find(const predicatet &predicate, unsigned &nr) const
    {
      predicate_mapt::const_iterator it=
        predicate_map.find(predicate);

      if(it==predicate_map.end())
        return false;

      nr=it->second;

      return true;
    }

    const predicatet &operator[](unsigned nr) const
    {
      return predicate_vector[nr]->first;
    }

    // how many?
    unsigned size() const
    {
      return predicate_vector.size();
    }

    static exprt make_expr_passive(
        const exprt& phi,
        const namespacet& ns,
        const unsigned subscript);

  protected:
    typedef std::map<predicatet, unsigned> predicate_mapt;
    typedef std::vector<predicate_mapt::iterator> predicate_vectort;

    predicate_mapt predicate_map;
    predicate_vectort predicate_vector;

    friend bool operator== (const predicatest &p1, const predicatest &p2);

    static void make_expr_passive_rec(
        exprt& phi,
        const namespacet& ns,
        const unsigned subscript);
};

std::ostream& operator<< (std::ostream& out,
    const predicatest &predicates);

inline bool operator!= (const predicatest &p1, const predicatest &p2)
{
  return !(p1==p2);
}

#endif
