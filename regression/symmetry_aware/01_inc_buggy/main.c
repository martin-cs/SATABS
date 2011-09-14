//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//A counter using locks

volatile unsigned value;

unsigned NonblockingCounter__increment() {
	unsigned v = 0;

#ifdef HPRED
	__CPROVER_predicate(v >= 1 + v);
#endif

	if(value == 0u-1) {
#ifdef USE_BRANCHING_ASSUMES
		__CPROVER_assume(value == 0u-1);
#endif

		return 0;
	}else{
#ifdef USE_BRANCHING_ASSUMES
		__CPROVER_assume(!(value == 0u-1));
#endif

		v = value;
		if(v == value){
#ifdef USE_BRANCHING_ASSUMES
      __CPROVER_assume(v == value);
#endif
      value = v + 1;
    }else{
#ifdef USE_BRANCHING_ASSUMES
      __CPROVER_assume(!(v == value));
#endif
      value = 0;
    }

		__CPROVER_assert(value > v,"error"); 

		return v + 1;
	}
}

int main(){
	while(1) { __CPROVER_ASYNC_01: NonblockingCounter__increment(); }
}
