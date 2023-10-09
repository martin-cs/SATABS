#include "../basics.h"

#define WORKPERTHREAD 2
#define THREADSMAX 3
volatile int max = 0x80000000;

int storage[WORKPERTHREAD*THREADSMAX];

#if (TPRED >= 1)
#define APRED 2
#endif

int cas_max(int e, int u){
#ifdef HPRED
	__CPROVER_parameter_predicates();
#endif

	int ret = -1;

#if (APRED >= 2)
__CPROVER_predicate(ret == 0);
#endif

	//atomic_begin();
	if (max == e) {
		assume(max == e);
		max = u; 
		//atomic_end();
		ret = 1;
	} else {
		assume(!(max == e));
		//atomic_end();
		ret = 0; 
	}
	
	return ret;
}


void findMax(int offset){
	int i;
	int e;
	int c; 
	int cret;

#if (APRED >= 1)
__CPROVER_predicate(c >= e);
#endif
#if (APRED >= 2)
__CPROVER_predicate(cret == 0);
#endif

	for(i = offset; i < offset+WORKPERTHREAD; i++) {
		e = storage[i];

		while(1){
			c = max;
			if(e > c){
				assume(e > c);
				cret = cas_max(c, e);
				if(cret){
					assume(cret);
					break;
				}else{
					assume(!(cret));
				}
			}else{
				assume(!(e > c));
				break;
			}
		}

		unsafe_assert(e <= max);
	}
}

int main() {
	int offset;
	assume(offset % WORKPERTHREAD == 0 && offset >= 0 && offset < WORKPERTHREAD*THREADSMAX);
	while(1) { __CPROVER_ASYNC_1: findMax(offset); }
}
