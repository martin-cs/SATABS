#define WORKPERTHREAD 2
#define THREADSMAX 3
volatile int max = 0x80000000;

int storage[WORKPERTHREAD*THREADSMAX];

int cas_max(int e, int u){
	__CPROVER_parameter_predicates();
	int ret = -1;

	__CPROVER_atomic_begin();
	if (max == e) {
		__CPROVER_assume(max == e);
		max = u; 
		__CPROVER_atomic_end();
		ret = 1;
	} else {
		__CPROVER_assume(!(max == e));
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
			__CPROVER_assume(e > my_max);
			my_max = e;
		}else{
			__CPROVER_assume(!(e > my_max));
		}
		assert(e <= my_max);
	}

	while(1){
		c = max;
		if(my_max > c){
			__CPROVER_assume(my_max > c);
			cret = cas_max(c, my_max);
			if(cret){
				__CPROVER_assume(cret);
				break;
			}else{
				__CPROVER_assume(!(cret));
			}
		}else{
			__CPROVER_assume(!(my_max > c));
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
