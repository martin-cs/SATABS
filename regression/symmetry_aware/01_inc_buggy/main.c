//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//A counter using locks

#include "../basics.h"

volatile unsigned value;

unsigned NonblockingCounter__increment() {
	unsigned v = 0;

#ifdef HPRED
	__CPROVER_predicate(v >= 1 + v);
#endif

	if(value == 0u-1) {
		assume(value == 0u-1);

		return 0;
	}else{
		assume(!(value == 0u-1));

		v = value;
		if(v == value){
      assume(v == value);
      value = v + 1;
    }else{
      assume(!(v == value));
      value = 0;
    }

		unsafe_assert(value > v); 

		return v + 1;
	}
}

int main(){
	while(1) { __CPROVER_ASYNC_01: NonblockingCounter__increment(); }
}
