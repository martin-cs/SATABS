/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROGRAM_FORMULA_H
#define CPROVER_PROGRAM_FORMULA_H

#include <string>
#include <vector>
#include <list>
#include <map>

#include <std_types.h>
#include <std_code.h>

#include <goto-programs/goto_program_template.h>

#include "formula.h"

class program_formulat
{
public:
  typedef formulat::variablet variablet;
  typedef formulat::variablest variablest;
  
  typedef std::map<irep_idt, unsigned> variable_mapt;

  typedef std::vector<irep_idt> eventst;
  typedef std::map<irep_idt, unsigned> event_mapt;
  
  unsigned no_globals, no_locals;
  
  class assignt
  {
  public:
    unsigned variable;
    formulat value;
    bool in_use;
  };
  
  class function_assignt
  {
  public:
    unsigned variable;
    bool in_use;
  };
  
  typedef std::vector<assignt> assignst;
  
  class formula_codet
  {
  public:
    // original code
    codet code_expr;
    exprt guard_expr;

    // for assign
    assignst assigns;
    formulat constraint;
    
    // for function calls
    irep_idt function;
    typedef std::vector<formulat> function_argst;
    typedef std::vector<function_assignt> function_lhst;
    function_lhst function_lhs;
    function_argst function_args;
    
    // for efficient history and partial order reduction
    bool can_form_cycle;
    
    // variables that are alive at this location
    std::set<unsigned> alive;
  };  

  class formula_goto_programt:public goto_program_templatet<formula_codet, formulat>
  {
  public:
    variablest *variables;
  
    virtual std::ostream& output_instruction(
      const namespacet &ns,
      const irep_idt &identifier,
      std::ostream &out,
      const_targett it) const;

    void find_cycles();
    
    formula_goto_programt():variables(NULL)
    {
    }
  };
  
  struct functiont
  {
    code_typet type;
    formula_goto_programt body;

    typedef std::vector<unsigned> argst;
    argst args;
    
    unsigned number_of_return_values;
  };

  typedef std::map<irep_idt, functiont> function_mapt;
  function_mapt function_map;

  void find_cycles();
  void compute_alive();

  variablest variables;
  variable_mapt variable_map;
  eventst events;
  event_mapt event_map;
  
  void show_alive(std::ostream &out) const;
  void show_cycles(const namespacet &ns, std::ostream &out) const;
  
  void show_statistics(std::ostream &out) const;
};

bool operator<(const program_formulat::formula_goto_programt::const_targett i1,
               const program_formulat::formula_goto_programt::const_targett i2);
               
std::ostream& operator<< (std::ostream& out,
                          const program_formulat::formula_goto_programt &program);

std::ostream& operator<< (std::ostream& out,
                          const program_formulat::variablest &variables);

#endif
