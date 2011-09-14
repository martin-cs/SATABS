//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//Listing 2. A nonblocking counter using CAS

volatile unsigned value = 0;

/*helpers for the property*/
volatile unsigned inc_flag = 0;
volatile unsigned dec_flag = 0;

unsigned NonblockingCounter__increment__01() {
	unsigned inc__v = 0, inc__vn = 0, inc__casret = 0;

	do {
		inc__v = value;

		if(inc__v == 0u-1) {
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(inc__v == 0u-1);
#endif
			return 0; /*increment failed, return min*/
		}else{
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(!(inc__v == 0u-1));
#endif
		}

		inc__vn = inc__v + 1;

		__CPROVER_atomic_begin();
		if (value == inc__v) {
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(value == inc__v);
#endif
			value = inc__vn;
			inc_flag = 1; /*set flag*/
			__CPROVER_atomic_end();
			inc__casret = 1; 
		} else {
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(!(value == inc__v));
#endif
			__CPROVER_atomic_end();
			inc__casret = 0; 
		}
	}
	while (inc__casret==0);
#ifdef USE_BRANCHING_ASSUMES
	__CPROVER_assume(!(inc__casret==0));
#endif

	//assert(dec_flag || value > inc__v);

	return inc__vn;
}

unsigned NonblockingCounter__decrement__01() {
	unsigned dec__v = 0, dec__vn = 0, dec__casret = 0;

	do {
		dec__v = value;

		if(dec__v == 0) {
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(dec__v == 0);
#endif
			return 0u-1; /*decrement failed, return max*/
		}else{
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(!(dec__v == 0));
#endif
		}
		
		dec__vn = dec__v - 1;

		__CPROVER_atomic_begin();
		__CPROVER_assert(value == dec__v,"error"); //unsafe
		if (value == dec__v) {
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(value == dec__v);
#endif
			value = dec__vn; 
			dec_flag = 1; /*set flag*/
			__CPROVER_atomic_end();
			dec__casret = 1; 
		} else {
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(!(value == dec__v));
#endif
			__CPROVER_atomic_end();
			dec__casret = 0; 
		}
	}
	while (dec__casret==0);
#ifdef USE_BRANCHING_ASSUMES
	__CPROVER_assume(!(dec__casret==0));
#endif
	//assert(inc_flag || value < dec__v);
	return dec__vn;
}

int main(){
	while(1) { 
		int r = rand();
		if(r){ __CPROVER_ASYNC_01: NonblockingCounter__increment__01(); }
		else{ __CPROVER_ASYNC_02: NonblockingCounter__decrement__01(); }
	}
}
