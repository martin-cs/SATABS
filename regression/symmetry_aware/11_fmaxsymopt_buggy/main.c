#include "../basics.h"

#define WORKPERTHREAD 2
#define THREADSMAX 3
volatile int max = 0x80000000;

int storage[WORKPERTHREAD*THREADSMAX];

void findMax(int offset){
	int i;
	int e;
	int my_max = 0x80000000;

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
		unsafe_assert(e <= my_max);
	}

	//atomic_begin();
	{
		if(my_max > max) {
			assume(my_max > max);
			max = my_max;
		}else{
			assume(!(my_max > max));
		}
	}
	//atomic_end();

	unsafe_assert(my_max <= max);
}

int main() {
	int offset;
	assume(offset % WORKPERTHREAD == 0 && offset >= 0 && offset < WORKPERTHREAD*THREADSMAX);
	while(1) { __CPROVER_ASYNC_1: findMax(offset); }
}
