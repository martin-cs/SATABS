#include "basics.h"

#define WORKPERTHREAD 2
#define THREADSMAX 3
volatile int max = 0;

int storage[WORKPERTHREAD*THREADSMAX];

void findMax(int offset){ //add offset???
	int i = -1;
	int e = -1;

	for(i = offset; i < offset+WORKPERTHREAD; i++) {
		assert(i < WORKPERTHREAD*THREADSMAX);
		e = storage[i];
		
		__CPROVER_atomic_begin();
		{
			if(e > max) {
				__CPROVER_assume(e > max);
				max = e;
			}else{
				__CPROVER_assume(!(e > max));
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
