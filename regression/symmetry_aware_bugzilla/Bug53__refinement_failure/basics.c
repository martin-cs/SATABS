#define basics_c
#include "basics.h"

#ifndef SATABS

#else

void atomic_begin(){
	__CPROVER_atomic_begin();
}

void atomic_end(){
	__CPROVER_atomic_end();
}
#endif

