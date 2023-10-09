//http://www.ibm.com/developerworks/java/library/j-jtp11234/
//Listing 5. Implementing a thread-safe PRNG with synchronization and atomic variables

#include "../basics.h"

#if (TPRED == 1)
#define APRED 1
#elif (TPRED >= 2)
#define APRED 3
#endif 

int calculateNext(int s2){ 
	int calculateNext_return;
#ifdef HPRED
	__CPROVER_parameter_predicates();
#endif
#if (APRED >= 2)
	//__CPROVER_predicate(calculateNext_return == read); //cannot be specified here
	__CPROVER_predicate(calculateNext_return == 0);
	__CPROVER_predicate(calculateNext_return == s2);
#endif

	do{
		calculateNext_return = rand();
	}while(calculateNext_return == s2 || calculateNext_return == 0);
	assume(!(calculateNext_return == s2 || calculateNext_return == 0));

	return calculateNext_return;
}

volatile int seed; 

int PseudoRandomUsingAtomic_nextInt(int n) {
	int read, nexts, nextInt_return;

#ifdef HPRED
	__CPROVER_predicate(n==10);
#endif
#if (APRED >= 3)
	__CPROVER_predicate(nextInt_return <= 10);
	__CPROVER_predicate(nexts % n <= 10);
	//__CPROVER_predicate(calculateNext_return % n <= 10); //cannot be specified here
#endif

	atomic_begin();
	read = seed;
	nexts = calculateNext(read);
	assert(nexts != read); 
	seed = nexts;
	atomic_end();
	nextInt_return = nexts % n;

	return nextInt_return;
}

void PseudoRandomUsingAtomic_monitor(){
	while(1){
		unsafe_assert(seed != 2);
	}
}

void PseudoRandomUsingAtomic_constructor(int init){

#if (APRED >= 1)
	__CPROVER_predicate(init == 0);
#endif

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
	while(1) { __CPROVER_ASYNC_01: PseudoRandomUsingAtomic__threadmain(); }
}
