#define WORKPERTHREAD 2
#define THREADSMAX 3
volatile int max = 0x80000000;

int storage[WORKPERTHREAD*THREADSMAX];

void findMax(int offset){
	int i;
	int e;
	int my_max = 0x80000000;

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

	__CPROVER_atomic_begin();
	{
		if(my_max > max) {
			__CPROVER_assume(my_max > max);
			max = my_max;
		}else{
			__CPROVER_assume(!(my_max > max));
		}
	}
	__CPROVER_atomic_end();

	assert(my_max <= max);
}

int main() {
	int offset;
	__CPROVER_assume(offset % WORKPERTHREAD == 0 && offset >= 0 && offset < WORKPERTHREAD*THREADSMAX);
	while(1) { __CPROVER_ASYNC_1: findMax(offset); }
}
