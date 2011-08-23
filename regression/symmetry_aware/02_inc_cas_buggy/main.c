//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//Listing 2. A nonblocking counter using CAS

#include "../basics.h"

volatile unsigned value;

unsigned NonblockingCounter__increment() {
	unsigned v,vn,casret;

	do {
		v = value;

		if(v != value) {
			assume(v != value);
			return 0; 
		}else{
			assume(!(v != value));
		}

		vn = v + 1;

		__CPROVER_atomic_begin();
		if (value == v) {
			assume(value == v);
			value = vn; 
			__CPROVER_atomic_end();
			casret = 1; 
		} else {
			assume(!(value == v));
			__CPROVER_atomic_end();
			casret = 0; 
		}
	}
	while (casret==0);
	assume(!(casret==0));
	safe_assert(value > v);

	return vn;
}

void caller(){
	int i;
	i = NonblockingCounter__increment();
	unsafe_assert(i != 0);
}

int main(){
	while(1) { __CPROVER_ASYNC_01: caller(); }
}
