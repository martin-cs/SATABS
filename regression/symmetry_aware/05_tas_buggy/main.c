//Simple test_and_set lock with exponential backoff
//
//From Algorithms for Scalable Synchronization on Shared-Memory Multiprocessors, 1991 (Fig. 1).
//Also available as pseudo-code here: http://www.cs.rochester.edu/research/synchronization/pseudocode/ss.html#tas

#include "../basics.h"

#if (TPRED >= 1)
#define APRED 2
#endif

enum lock_t {unlocked, locked};
volatile enum lock_t lock = unlocked;

enum lock_t TestAndSet() {
	enum lock_t oldValue;

#if (APRED >= 1)
	__CPROVER_predicate(oldValue == locked);
	__CPROVER_predicate(oldValue == lock);
#endif

	//atomic_begin();
	oldValue = lock;
	lock = locked;
	//atomic_end();

	return oldValue;
}

void acquire_lock(){
	int delay;
	enum lock_t cond;

#if (APRED >= 1)
	__CPROVER_predicate(cond == locked);
#endif

	delay = 1;
	cond = TestAndSet();
	while(cond == locked){
#ifdef USE_BRANCHING_ASSUMES
		assume(cond == locked);
#endif
		pause(delay);
		if(delay*2 > delay) 
			delay *= 2;
		cond = TestAndSet();		
	}
#ifdef USE_BRANCHING_ASSUMES
	assume(!(cond == locked));
#endif
	unsafe_assert(cond != lock);
	assume(cond != lock);
}

void release_lock(){
	unsafe_assert(lock != unlocked);
	assume(lock != unlocked);
	lock = unlocked; 
}

int c = 0;
void TAS_backoff__main(){
#if (APRED >= 2)
	__CPROVER_predicate(c == 0);
	__CPROVER_predicate(lock == locked);
#endif
	while(1){
		acquire_lock();
		c++; 
		//unsafe_assert(c == 1); 
		//assume(c==1);
		c--;
		release_lock();
	}
}

int main(){
	while(1) { __CPROVER_ASYNC_1: TAS_backoff__main(); }
}
