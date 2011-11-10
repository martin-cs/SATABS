#ifndef BASICS
#define BASICS

//#define null ((void*)0xFFFFFFFF)
#define null 0
typedef int index_type;
typedef int univ_ptr_t;
#define MAX_ELEM 5

#ifndef SATABS
#define PREDICATE(e)
#define PARAPREDS
#define PRETPREDS
extern void atomic_begin();
extern void atomic_end();
extern void pause(int);
#include <assert.h>
#else
#define PREDICATE(e) __CPROVER_predicate(e)
#define PARAPREDS __CPROVER_parameter_predicates();
#define PRETPREDS __CPROVER_return_predicates();
void __CPROVER_atomic_begin();
void atomic_begin();
void __CPROVER_atomic_end();
void atomic_end();
extern void pause(int);
#define assert(e) __CPROVER_assert(e,"bla")
#endif

#endif
