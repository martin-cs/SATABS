#define WORKPERTHREAD 2
#define THREADSMAX 3
volatile int max = 0x80000000;

int storage[WORKPERTHREAD*THREADSMAX];

void findMax(int offset){
	int i;
	int e;

	for(i = offset; i < offset+WORKPERTHREAD; i++) {
		e = storage[i];
		
		__CPROVER_atomic_begin();
		{
			if(e > max) {
#ifdef USE_BRANCHING_ASSUMES
				__CPROVER_assume(e > max);
#endif
				max = e;
			}else{
#ifdef USE_BRANCHING_ASSUMES
				__CPROVER_assume(!(e > max));
#endif
			}
		}
		__CPROVER_atomic_end();
		assert(e <= max);
	}
}

int main() {
	int offset;
	__CPROVER_assume(offset % WORKPERTHREAD == 0 && offset >= 0 && offset < WORKPERTHREAD*THREADSMAX);
	while(1) { __CPROVER_ASYNC_1: findMax(offset); }
}
