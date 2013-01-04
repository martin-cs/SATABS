/*******************************************************************\

Module: Statistics

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#include <assert.h>

#include "program_formula.h"

/*******************************************************************\

Function: program_formulat::show_statistics

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void program_formulat::show_statistics(std::ostream &out) const
{
  out << "Total number of functions...: "
      << function_map.size() << std::endl;

  out << "Total number of variables...: "
      << variables.size() << std::endl;

  out << "  Global variables..........: "
      << no_globals << std::endl;

  out << "  Local variables...........: "
      << no_locals << std::endl;

  //unsigned max_local_variables=0;
  unsigned assignments=0;

  for(function_mapt::const_iterator
      f_it=function_map.begin();
      f_it!=function_map.end();
      f_it++)
  {
    const formula_goto_programt &program=f_it->second.body;
  
    for(formula_goto_programt::instructionst::const_iterator
        i_it=program.instructions.begin();
        i_it!=program.instructions.end();
        i_it++)
    {
      const formula_goto_programt::instructiont
        &instruction=*i_it;

      #if 0
      max_local_variables=std::max(
        max_local_variables,
        unsigned(instruction.local_variables.size()));
      #endif
      
      if(instruction.is_assign())
        assignments++;
    }
  }

  #if 0
  out << "  Max. used local variables.: "
      << max_local_variables << std::endl;
  #endif

  out << "Assignments.................: "
      << assignments << std::endl;
}
