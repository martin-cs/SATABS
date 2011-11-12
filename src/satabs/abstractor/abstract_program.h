/*******************************************************************\

Module: An Abstract Transition System

Author: Daniel Kroening

Date: January 2004

\*******************************************************************/

#ifndef CPROVER_CEGAR_ABSTRACT_PROGRAM_H
#define CPROVER_CEGAR_ABSTRACT_PROGRAM_H

#include <memory>

#include <goto-programs/goto_program_template.h>
#include <goto-programs/goto_functions_template.h>

#include "../prepare/concrete_program.h"
#include "abstract_transition_relation.h"

// A basic abstract instruction holds both the equation, and the resulting cubes 
class abstract_codet
{
private:
  std::auto_ptr<abstract_transition_relationt> transition_relation;
  
public:
  // for convenience, keep pointer to concrete block
  goto_programt::const_targett concrete_pc;
  
  // for efficiency, mark if this location
  // needs to be re-abstracted
  bool re_abstract;

  abstract_codet():
    transition_relation(std::auto_ptr<abstract_transition_relationt>(NULL)),
    re_abstract(false)
  {
  }

  abstract_codet(const abstract_codet &other):
    transition_relation(
      other.transition_relation.get() == NULL ? 
        std::auto_ptr<abstract_transition_relationt>(NULL) : 
        std::auto_ptr<abstract_transition_relationt>(new abstract_transition_relationt(*(other.transition_relation)))),
    concrete_pc(other.concrete_pc),
    re_abstract(other.re_abstract)
  {

  }

  abstract_codet & operator = (const abstract_codet &other)
  {
    transition_relation=
      other.transition_relation.get() == NULL ? 
        std::auto_ptr<abstract_transition_relationt>(NULL) : 
        std::auto_ptr<abstract_transition_relationt>(new abstract_transition_relationt(*(other.transition_relation)));
    concrete_pc = other.concrete_pc;
    re_abstract = other.re_abstract;
    return *this;
  }

  abstract_transition_relationt& get_transition_relation() const
  {
    return *transition_relation;
  }

  void set_transition_relation(std::auto_ptr<abstract_transition_relationt> transition_relation)
  {
    this->transition_relation = transition_relation;
  }

};

class abstract_programt:public goto_program_templatet<abstract_codet, exprt>
{
public:
  virtual std::ostream& output_instruction(
    const namespacet &ns,
    const irep_idt &identifier,
    std::ostream &out,
    const_targett it) const;
};

bool operator<(const abstract_programt::const_targett i1,
               const abstract_programt::const_targett i2);

typedef goto_functions_templatet<abstract_programt> abstract_functionst;
 
#endif
