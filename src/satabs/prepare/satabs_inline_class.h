/*
 * satabs_inline_class.h
 *
 * Temporary inliner to allow CAV'11 functionality to be transferred to mainline SatAbs
 *
 * This is practically a *duplicate* of satabs_inline_class.h, and should be removed
 * as soon as refinement works
 *
 *  Created on: Aug 3, 2011
 *      Author: alad
 */

#ifndef SATABS_INLINE_CLASS_H_
#define SATABS_INLINE_CLASS_H_

#include <message_stream.h>

#include <goto-programs/goto_functions.h>

class satabs_inlinet:public message_streamt
{
public:
  satabs_inlinet(
    goto_functionst &_goto_functions,
    const namespacet &_ns,
    message_handlert &_message_handler):
    message_streamt(_message_handler),
    smallfunc_limit(0),
    goto_functions(_goto_functions),
    ns(_ns)
  {
  }

  void satabs_inline(goto_programt &dest);

  void satabs_inline_rec(
    goto_functionst::function_mapt::iterator,
    bool full);

  void satabs_inline_rec(goto_programt &dest, bool full);

  // inline single instruction at 'target'
  // returns true in case a change was done
  // set 'full' to perform this recursively
  bool inline_instruction(
    goto_programt &dest,
    bool full,
    goto_programt::targett &target);

  unsigned smallfunc_limit;

protected:
  goto_functionst &goto_functions;
  const namespacet &ns;

  void expand_function_call(
    goto_programt &dest,
    goto_programt::targett &target,
    const exprt &lhs,
    const exprt &function,
    const exprt::operandst &arguments,
    const exprt &constrain,
    bool recursive);

  void satabs_replace_return(
    goto_programt &body,
    const exprt &lhs,
    const exprt &constrain,
    bool add_return_predicates);

  void parameter_assignments(
    const locationt &location,
    const irep_idt &function_name,
    const code_typet &code_type,
    const exprt::operandst &arguments,
    goto_programt &dest,
    bool add_parameter_predicates
    );

  typedef hash_set_cont<irep_idt, irep_id_hash> recursion_sett;
  recursion_sett recursion_set;

  typedef hash_set_cont<irep_idt, irep_id_hash> no_body_sett;
  no_body_sett no_body_set;

  typedef hash_set_cont<irep_idt, irep_id_hash> finished_inlining_sett;
  finished_inlining_sett finished_inlining_set;
};


#endif /* SATABS_INLINE_CLASS_H_ */
