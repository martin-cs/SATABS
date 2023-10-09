/*
 * satabs_inline.h
 *
 *  Created on: Aug 3, 2011
 *      Author: alad
 */

#ifndef CPROVER_SATABS_SATABS_INLINE_H
#define CPROVER_SATABS_SATABS_INLINE_H

#include <goto-programs/goto_functions.h>

class message_handlert;
class namespacet;

// do a full inlining
void satabs_inline(
    goto_functionst &goto_functions,
    const namespacet &ns,
    message_handlert &message_handler);

// inline those functions marked as "inlined"
// and functions with less than _smallfunc_limit instructions
void satabs_partial_inline(
    goto_functionst &goto_functions,
    const namespacet &ns,
    message_handlert &message_handler,
    unsigned _smallfunc_limit = 0);

#endif
