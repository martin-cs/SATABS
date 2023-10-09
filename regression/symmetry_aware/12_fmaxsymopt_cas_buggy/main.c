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

	atomic_begin();
	if (max == e) {
		assume(max == e);
		max == u;  //== instead of =
		atomic_end();
		ret = 1;
	} else {
		assume(!(max == e));
		atomic_end();
		ret = 0; 
	}

	return ret;
}

void findMax(int offset){
	int i;
	int e;
	int my_max = 0x80000000;
	int c; 
	int cret;

#if (APRED >= 1)
	__CPROVER_predicate(c >= my_max);
#endif
#if (APRED >= 2)
	__CPROVER_predicate(cret == 0);
#endif
	while(rand())
	//for(i = offset; i < offset+WORKPERTHREAD; i++) 
	{
		i = rand();
		assume(i < WORKPERTHREAD*THREADSMAX);
		e = storage[i];

		if(e > my_max) {
			assume(e > my_max);
			my_max = e;
		}else{
			assume(!(e > my_max));
		}
		safe_assert(e <= my_max);
	}

	while(1){
		c = max;
		if(my_max > c){
			assume(my_max > c);
			cret = cas_max(c, my_max);
			if(cret){
				assume(cret);
				break;
			}else{
				assume(!(cret));
			}
		}else{
			assume(!(my_max > c));
			break;
		}
	}

	unsafe_assert(my_max <= max);
}

int main() {
	int offset;
	assume(offset % WORKPERTHREAD == 0 && offset >= 0 && offset < WORKPERTHREAD*THREADSMAX);
	while(1) { __CPROVER_ASYNC_1: findMax(offset); }
}
