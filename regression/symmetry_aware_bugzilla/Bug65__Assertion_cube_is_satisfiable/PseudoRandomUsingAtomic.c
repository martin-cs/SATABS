//http://www.ibm.com/developerworks/java/library/j-jtp11234/
//Listing 5. Implementing a thread-safe PRNG with synchronization and atomic variables
//
//06/12/2010 -- Transformed to C
//11/01/2011 -- Restructured

#include "basics.h"
int rand();

int calculateNext(int s2){ //some functionality to make the return value depend on the argument
	int ret3;
#ifdef HPRED
	PARAPREDS;
	PRETPREDS;
	PREDICATE(ret3 == s2);
#endif
	do{
		ret3 = rand();
	}while(ret3 == s2);
	assume(ret3 != s2);

	return ret3;
}

volatile int seed; //concurrently accessed

int PseudoRandomUsingAtomic_compareAndSet(int expect, int update) 
{
#ifdef HPRED
	PARAPREDS;
	PRETPREDS;
	PREDICATE(seed == expect);	
	PREDICATE(seed == update);
#endif
	atomic_begin();
	if (seed == expect) {
		seed = update; 
		atomic_end();
		return 1; 
	}
	atomic_end();
	return 0; 
}

void PseudoRandomUsingAtomic_constructor(int s3){
#ifdef HPRED
	PARAPREDS;
	PREDICATE(seed == s3);
#endif
	seed = s3;
}

int PseudoRandomUsingAtomic_nextInt(int n) {
	int s1, nexts, ret2, ret4;

#ifdef HPRED
	PARAPREDS;
	PREDICATE(n==10);
#endif

	while(1) {
		s1 = seed;
		nexts = calculateNext(s1);
		assert(nexts != s1); //property
		ret4 = PseudoRandomUsingAtomic_compareAndSet(s1, nexts);
		if(ret4 == 1){
      assume(ret4 == 1);
			ret2 = s1 % n;
			return ret2;
		}
	}
}

void PseudoRandomUsingAtomic__init(){ //called once at the beginning
  //not needed with Satabs
}

void PseudoRandomUsingAtomic__threadmain(){ //potentially called by arbitrary many threads concurrently
	int ret1, range;
	
	ret1 = PseudoRandomUsingAtomic_nextInt(10);
	assert(ret1<=10); //property
}

int main(){
	PseudoRandomUsingAtomic__init();
	while(1) __CPROVER_ASYNC_01: PseudoRandomUsingAtomic__threadmain();
}
