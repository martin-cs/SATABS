/*******************************************************************\

Module: Counterexamples

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#include <assert.h>

#include "abstract_state.h"

/*******************************************************************\

Function: abstract_stept::output

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void abstract_stept::output(std::ostream &out) const
{
  switch(step_type)
  {
    case STATE:
      if(has_pc)
      {
        out << "// " << pc->location << std::endl;
        out << pc->type;

        if(pc->is_goto())
          out << " branch_taken=" << branch_taken;
      }
      else
        out << "// no PC" << std::endl;

      out << std::endl;

      for(thread_to_predicate_valuest::const_iterator
          it=thread_states.begin();
          it!=thread_states.end(); it++)
      {
        out << "  thread " << it->first << ": (";
        for(unsigned i = 0; i < it->second.size(); i++)
        {
          out << "b" << i << " = " << it->second[i];
          if(i < it->second.size() - 1) out << " ";
        }
        out << ")" << std::endl;
      }

      out << std::endl;
      break;

    case LOOP_BEGIN:
      out << "===== LOOP [:" << std::endl;
      break;

    case LOOP_END:
      out << "===== LOOP :]" << std::endl;
      break;

    default:
      assert(false);
  }
}

/*******************************************************************\

Function: operator <<

Inputs:

Outputs:

Purpose:

\*******************************************************************/

std::ostream &operator<<(
    std::ostream &out,
    const abstract_stept &step)
{
  step.output(out);
  return out;
}

