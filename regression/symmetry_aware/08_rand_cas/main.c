//http://www.ibm.com/developerworks/java/library/j-jtp11234/
//Listing 5. Implementing a thread-safe PRNG with synchronization and atomic variables

int calculateNext(int s2){ 
	int calculateNext_return;
#ifdef HPRED
	__CPROVER_parameter_predicates();
#endif
	do{
		calculateNext_return = rand();
	}while(calculateNext_return == s2 || calculateNext_return == 0);
#ifdef USE_BRANCHING_ASSUMES
	__CPROVER_assume(!(calculateNext_return == s2 || calculateNext_return == 0));
#endif

	return calculateNext_return;
}

volatile int seed; 

int PseudoRandomUsingAtomic_compareAndSet(int expect, int update) 
{
	__CPROVER_atomic_begin();
	if (seed == expect) {
#ifdef USE_BRANCHING_ASSUMES
		__CPROVER_assume(seed == expect);
#endif
		seed = update; 
		__CPROVER_atomic_end();
		return 1; 
	}else{
#ifdef USE_BRANCHING_ASSUMES
		__CPROVER_assume(!(seed == expect));
#endif
		__CPROVER_atomic_end();
		return 0; 
	}
}

int PseudoRandomUsingAtomic_nextInt(int n) {
	int read, nexts, casret, nextInt_return;
#ifdef HPRED
	__CPROVER_predicate(n==10);
#endif

	while(1) {
		read = seed;
		nexts = calculateNext(read);
		assert(nexts != read); 
		casret = PseudoRandomUsingAtomic_compareAndSet(read, nexts);
		if(casret == 1){
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(casret == 1);
#endif
			nextInt_return = nexts % n;
			break;
		}else{
#ifdef USE_BRANCHING_ASSUMES
			__CPROVER_assume(!(casret == 1));
#endif
		}
	}

	return nextInt_return;
}

void PseudoRandomUsingAtomic_monitor(){
	while(1){
		assert(seed != 0);
	}
}

void PseudoRandomUsingAtomic_constructor(int init){
	seed = init;
}

void PseudoRandomUsingAtomic__threadmain(){ 
	int myrand;

	myrand = PseudoRandomUsingAtomic_nextInt(10);
	assert(myrand <= 10);
}

int main(){
	PseudoRandomUsingAtomic_constructor(1);
	__CPROVER_ASYNC_00: PseudoRandomUsingAtomic_monitor();
	while(1) __CPROVER_ASYNC_01: PseudoRandomUsingAtomic__threadmain();
}
