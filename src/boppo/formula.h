/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FORMULA_H
#define CPROVER_FORMULA_H

#include <iostream>
#include <list>
#include <set>

#include <solvers/prop/prop.h>

class formula_nodet
{
public:
  friend class formula_containert;

  typedef enum { NONE, VARIABLE, NEXT_VARIABLE,
                 NONDET, CONST_TRUE, CONST_FALSE,
                 AND, NOT, OR, IFF, XOR } idt;

  idt id;
  unsigned variable;
  formula_nodet *a, *b;
  
  // constructors
  formula_nodet():id(NONE), variable(0), a(NULL), b(NULL), l_is_set(false)
  {
  }

  formula_nodet(idt _id):id(_id), variable(0), a(NULL), b(NULL), l_is_set(false)
  {
  }

  formula_nodet(idt _id, unsigned _variable):
    id(_id), variable(_variable), a(NULL), b(NULL), l_is_set(false)
  {
  }

  formula_nodet(idt _id, formula_nodet *_a):
    id(_id), variable(0), a(_a), b(NULL), l_is_set(false)
  {
  }

  formula_nodet(idt _id, formula_nodet *_a, formula_nodet *_b):
    id(_id), variable(0), a(_a), b(_b), l_is_set(false)
  {
  }

  literalt l;
  bool l_is_set;

  static formula_nodet true_node, false_node;
};

class formulat
{
protected:
  formula_nodet *node;

  friend class formula_containert;

public:
  class variablet
  {
  public:
    irep_idt description;
    irep_idt identifier, base_name, display_name;
    bool is_global;
  };
  
  typedef std::vector<variablet> variablest;
  
  explicit formulat(formula_nodet *_node):node(_node)
  {
  }
  
  formulat():node(NULL)
  {
  }
  
  formula_nodet *get_node() const
  {
    return node;
  }
  
  bool is_null() const { return node==NULL; }
  bool is_true() const { return node->id==formula_nodet::CONST_TRUE; }
  bool is_false() const { return node->id==formula_nodet::CONST_FALSE; }
  bool is_constant() const { return is_true() || is_false(); }
  bool is_nondet() const { return node->id==formula_nodet::NONDET; }
  bool is_variable() const { return node->id==formula_nodet::VARIABLE; }
  void make_false() { node=&formula_nodet::false_node; }
  void make_true() { node=&formula_nodet::true_node; }
  
  void get_variables(std::set<unsigned> &variables) const;

  void get_global_variables(
    std::set<unsigned> &variable_set,
    const variablest &variables) const;

  void get_nondet_literals(std::set<literalt> &literals) const;
  
  literalt convert(propt &prop) const;
  
  void output(std::ostream &out, const variablest &variables) const;
  void output(std::ostream &out) const;
  
  formulat a() const
  {
    return formulat(node->a);
  }
  
  formulat b() const
  {
    return formulat(node->b);
  }
  
  formula_nodet::idt id() const
  {
    return node->id;
  }
  
  unsigned variable() const
  {
    return node->variable;
  }
  
  bool operator==(formulat other) const
  {
    return other.node==node;
  }

  bool operator!=(formulat other) const
  {
    return other.node!=node;
  }

protected:
  void output_op(
    std::ostream &out,
    const formulat op,
    const variablest &variables) const;

  void output_op(
    std::ostream &out,
    const formulat op) const;
};

class formula_containert
{
public:
  formulat new_node()
  {
    node_list.push_back(formula_nodet());
    return formulat(&node_list.back());
  }

  formulat new_node(const formula_nodet &_node)
  {
    node_list.push_back(_node);
    return formulat(&node_list.back());
  }

  formulat new_node(formula_nodet::idt _id)
  {
    return new_node(formula_nodet(_id));
  }

  formulat new_node(formula_nodet::idt _id, unsigned _variable)
  {
    return new_node(formula_nodet(_id, _variable));
  }

  formulat new_node(formula_nodet::idt _id, formulat _a)
  {
    return new_node(formula_nodet(_id, _a.get_node()));
  }

  formulat new_node(formula_nodet::idt _id, formulat _a, formulat _b)
  {
    return new_node(formula_nodet(_id, _a.get_node(), _b.get_node()));
  }
  
  formula_containert()
  {
  }
  
  formulat gen_and(formulat a, formulat b);
  formulat gen_or(formulat a, formulat b);
  formulat gen_not(formulat a);
  formulat gen_nondet() { return new_node(formula_nodet::NONDET); }
  formulat gen_if(formulat cond, formulat a, formulat b);  
  formulat duplicate(formulat a);  
  formulat gen_false() { return formulat(&formula_nodet::false_node); }
  formulat gen_true() { return formulat(&formula_nodet::true_node); }
  void reset_prop();
  void get_nondet_literals(std::set<literalt> &literals) const;

protected:
  typedef std::list<formula_nodet> node_listt;
  node_listt node_list;
}; 

#endif
