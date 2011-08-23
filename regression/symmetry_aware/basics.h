#ifndef BASICS
#define BASICS

#define null 0
typedef int index_type;
typedef int univ_ptr_t;
#define MAX_ELEM 5

#ifndef SATABS
//User-defined Predicates
#define PREDICATE(e)
#define PARAPREDS
#define PRETPREDS
#define RETPREDS

//Atomicity
extern void atomic_begin();
extern void atomic_end();

//Misc
extern void pause(int);
#include <assert.h>

#else
//User-defined Predicates
#define PREDICATE(e) __CPROVER_predicate(e)
#define PARAPREDS __CPROVER_parameter_predicates();
#define PRETPREDS __CPROVER_return_predicates();
#define RETPREDS __CPROVER_return_predicates();

//Atomicity
void __CPROVER_atomic_begin();
void __CPROVER_atomic_end();
void atomic_end();
void atomic_begin();

//Misc
void pause(int);
extern int rand();
#define assert(e) __CPROVER_assert(e,"bla")
#define assume(e) __CPROVER_assume(e)
#define safe_assert(e) __CPROVER_assert(e,"this property holds")
#define unsafe_assert(e) __CPROVER_assert(e,"this property can be violated")
#endif

#endif
