#define WORKPERTHREAD 2
#define THREADSMAX 3
volatile int max = 0x80000000;

int storage[WORKPERTHREAD*THREADSMAX];

int cas_max(int e, int u){
#ifdef HPRED
	__CPROVER_parameter_predicates();
#endif
	int ret = -1;

	__CPROVER_atomic_begin();
	if (max == e) {
#ifdef USE_BRANCHING_ASSUMES
		__CPROVER_assume(max == e);
#endif
		max = u; 
		__CPROVER_atomic_end();
		ret = 1;
	} else {
#ifdef USE_BRANCHING_ASSUMES
		__CPROVER_assume(!(max == e));
#endif
		__CPROVER_atomic_end();
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

	for(i = offset; i < offset+WORKPERTHREAD; i++) {
		e = storage[i];

		if(e > my_max) {
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(e > my_max);
#endif
			my_max = e;
		}else{
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(!(e > my_max));
#endif
		}
		assert(e <= my_max);
	}

	while(1){
		c = max;
		if(my_max > c){
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(my_max > c);
#endif
			cret = cas_max(c, my_max);
			if(cret){
#ifdef USE_BRANCHING_ASSUMES
				__CPROVER_assume(cret);
#endif
				break;
			}else{
#ifdef USE_BRANCHING_ASSUMES
				__CPROVER_assume(!(cret));
#endif
			}
		}else{
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(!(my_max > c));
#endif
			break;
		}
	}

	assert(my_max <= max);
}

int main() {
	int offset;
	__CPROVER_assume(offset % WORKPERTHREAD == 0 && offset >= 0 && offset < WORKPERTHREAD*THREADSMAX);
	while(1) { __CPROVER_ASYNC_1: findMax(offset); }
}
