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
extern void atomic_begin();
extern void atomic_end();
#else
#define PREDICATE(e) __CPROVER_predicate(e)
#define PARAPREDS __CPROVER_parameter_predicates();
void __CPROVER_atomic_begin();
void atomic_begin();
void __CPROVER_atomic_end();
void atomic_end();
#endif

#endif
