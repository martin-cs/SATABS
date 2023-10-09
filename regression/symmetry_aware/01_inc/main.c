//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//A counter using locks
volatile unsigned value;

unsigned NonblockingCounter__increment() {
	unsigned v = 0;

	__CPROVER_atomic_begin();
	if(value == 0u-1) {
#ifdef USE_BRANCHING_ASSUMES
		__CPROVER_assume(value == 0u-1);
#endif
		__CPROVER_atomic_end();

		return 0;
	}else{
#ifdef USE_BRANCHING_ASSUMES
		__CPROVER_assume(!(value == 0u-1));
#endif

		v = value;
		value = v + 1;
		__CPROVER_atomic_end();

		assert(value > v); 

		return v + 1;
	}
}

int main(){
	while(1) { __CPROVER_ASYNC_01: NonblockingCounter__increment(); }
}
