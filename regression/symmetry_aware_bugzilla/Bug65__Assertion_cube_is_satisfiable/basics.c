#define basics_c
#include "basics.h"

#ifndef SATABS
#include "Windows.h"
void pause(int d){
	Sleep(d);
}
#else
void atomic_begin(){
	__CPROVER_atomic_begin();
}

void atomic_end(){
	__CPROVER_atomic_end();
}

void pause(int d){
}
#endif
