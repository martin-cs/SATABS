#include "../basics.h"
int max = -1;

void findMax(){
	int e;
	e = rand();
	__CPROVER_assume(e >= 0);

	if(e > max) {
		__CPROVER_assume(e > max);
		max = e;
	}else{
		__CPROVER_assume(!(e > max));
	}
	unsafe_assert(e <= max);
}

int main() {
	while(1) { __CPROVER_ASYNC_1: findMax(); }
}
