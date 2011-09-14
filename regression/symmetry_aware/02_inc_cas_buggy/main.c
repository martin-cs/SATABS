//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//Listing 2. A nonblocking counter using CAS

volatile unsigned value;

unsigned NonblockingCounter__increment() {
	unsigned v,vn,casret;

	do {
		v = value;

		if(v != value) {
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(v != value);
#endif
			return 0; 
		}else{
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(!(v != value));
#endif
		}

		vn = v + 1;

		__CPROVER_atomic_begin();
		if (value == v) {
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(value == v);
#endif
			value = vn; 
			__CPROVER_atomic_end();
			casret = 1; 
		} else {
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(!(value == v));
#endif
			__CPROVER_atomic_end();
			casret = 0; 
		}
	}
	while (casret==0);
#ifdef USE_BRANCHING_ASSUMES
	__CPROVER_assume(!(casret==0));
#endif
	__CPROVER_assert(value > v,"error"); //safe

	return vn;
}

void caller(){
	int i;
	i = NonblockingCounter__increment();
	__CPROVER_assert(i != 0,"error"); //unsafe
}

int main(){
	while(1) { __CPROVER_ASYNC_01: caller(); }
}
