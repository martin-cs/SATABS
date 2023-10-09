//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//Listing 2. A counter using locks
volatile unsigned value = 0;

/*helpers for the property*/
volatile unsigned inc_flag = 0;
volatile unsigned dec_flag = 0;

unsigned NonblockingCounter__increment__01() {
	unsigned inc_v = 0;

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

		inc_v = value;
		value = inc_v + 1;
		inc_flag = 1; /*set flag*/
		__CPROVER_atomic_end();

		assert(dec_flag || value > inc_v);

		return inc_v + 1;
	}
}

unsigned NonblockingCounter__decrement__01() {
	unsigned dec_v;

	__CPROVER_atomic_begin();
	if(value == 0) {
#ifdef USE_BRANCHING_ASSUMES
		__CPROVER_assume(value == 0);
#endif
		__CPROVER_atomic_end();

		return 0u-1; /*decrement failed, return max*/
	}else{
#ifdef USE_BRANCHING_ASSUMES
		__CPROVER_assume(!(value == 0));
#endif

		dec_v = value;
		value = dec_v - 1;
		dec_flag = 1; /*set flag*/
		__CPROVER_atomic_end();

		assert(inc_flag || value < dec_v);

		return dec_v - 1;
	}
}

void NonblockingCounter__main__01(){
	int r = -1;
	r = rand();

	if(r){ NonblockingCounter__increment__01(); }
	else{ NonblockingCounter__decrement__01(); }
}

int main(){
	while(1) { __CPROVER_ASYNC_01: NonblockingCounter__main__01(); }
}
