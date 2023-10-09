//http://www.ibm.com/developerworks/java/library/j-jtp11234/
//Listing 5. Implementing a thread-safe PRNG with synchronization and atomic variables

#include "../basics.h"

#if (TPRED == 1)
#define APRED 1
#elif (TPRED >= 2)
#define APRED 4
#endif 

//These cannot be user-defined in this file (but in main_exp)
//#if (APRED >= 2)
//__CPROVER_predicate(calculateNext_return == read);
//#endif
//
//#if (APRED >= 4)
//__CPROVER_predicate(calculateNext_return % n <= 10);
//#endif

int flag = 0;

int calculateNext(int s2){ 
	int calculateNext_return;
#ifdef HPRED
	__CPROVER_parameter_predicates();
#endif
#if (APRED >= 2)
__CPROVER_predicate(calculateNext_return == 0);
__CPROVER_predicate(calculateNext_return == s2);
#endif
	do{
		calculateNext_return = rand();
	}while(calculateNext_return == s2 || calculateNext_return == 0);
	assume(!(calculateNext_return == s2 || calculateNext_return == 0));

	if(!flag){
		flag = 1;
		calculateNext_return = 4;
	}

	return calculateNext_return;
}

volatile int seed; 

int PseudoRandomUsingAtomic_compareAndSet(int expect, int update) 
{
#if (APRED >= 3)
__CPROVER_predicate(update == 0);
__CPROVER_predicate(seed == expect);
#endif

	atomic_begin();
	if (seed == expect) {
		assume(seed == expect);
		seed = update; 
		atomic_end();
		return 1; 
	}else{
		assume(!(seed == expect));
		atomic_end();
		return 0; 
	}
}

int PseudoRandomUsingAtomic_nextInt(int n) {
	int read, nexts, casret, nextInt_return;

#ifdef HPRED
	__CPROVER_predicate(n==10);
#endif
#if (APRED >= 3)
__CPROVER_predicate(seed == read);
__CPROVER_predicate(nexts == 0);
#endif
#if (APRED >= 4)
__CPROVER_predicate(casret == 1);
__CPROVER_predicate(nexts % n <= 10);
__CPROVER_predicate(nextInt_return <= 10);
#endif

	while(1) {
		read = seed;
		nexts = calculateNext(read);
		assert(nexts != read); 
		casret = PseudoRandomUsingAtomic_compareAndSet(read, nexts);
		if(casret == 1){
			assume(casret == 1);
			nextInt_return = nexts % n;
			break;
		}else{
			assume(!(casret == 1));
		}
	}

	return nextInt_return;
}

void PseudoRandomUsingAtomic_monitor(){
	while(1){
		assert(seed != 0);
		assert(seed < 10);
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
	while(1) __CPROVER_ASYNC_01: PseudoRandomUsingAtomic__threadmain();
}
