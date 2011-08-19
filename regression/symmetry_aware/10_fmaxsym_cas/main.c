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
	int c; 
	int cret;

	for(i = offset; i < offset+WORKPERTHREAD; i++) {
		e = storage[i];

		while(1){
			c = max;
			if(e > c){
				__CPROVER_assume(e > c);
				cret = cas_max(c, e);
				if(cret){
					__CPROVER_assume(cret);
					break;
				}else{
					__CPROVER_assume(!(cret));
				}
			}else{
				__CPROVER_assume(!(e > c));
				break;
			}
		}

		assert(e <= max);
	}
}

int main() {
	int offset;
	__CPROVER_assume(offset % WORKPERTHREAD == 0 && offset >= 0 && offset < WORKPERTHREAD*THREADSMAX);
	while(1) { __CPROVER_ASYNC_1: findMax(offset); }
}
