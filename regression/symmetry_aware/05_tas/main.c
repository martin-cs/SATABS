//Simple test_and_set lock with exponential backoff
//
//From Algorithms for Scalable Synchronization on Shared-Memory Multiprocessors, 1991 (Fig. 1).
//Also available as pseudo-code here: http://www.cs.rochester.edu/research/synchronization/pseudocode/ss.html#tas
enum lock_t {unlocked, locked};
volatile enum lock_t lock = unlocked;

enum lock_t TestAndSet() {
	enum lock_t oldValue;

	__CPROVER_atomic_begin();
	oldValue = lock;
	lock = locked;
	__CPROVER_atomic_end();

	return oldValue;
}

void acquire_lock(){
	int delay;
	enum lock_t cond;

	delay = 1;
	cond = TestAndSet();
	while(cond == locked){
#ifdef USE_BRANCHING_ASSUMES
		__CPROVER_assume(cond == locked);
#endif
		pause(delay);
		if(delay*2 > delay) 
			delay *= 2;
		cond = TestAndSet();		
	}
#ifdef USE_BRANCHING_ASSUMES
	__CPROVER_assume(!(cond == locked));
#endif
	assert(cond != lock);
}

void release_lock(){
	assert(lock != unlocked);
	lock = unlocked; 
}

int c = 0;
void TAS_backoff__main(){
	while(1){
		acquire_lock();
		c++; assert(c == 1); c--;
		release_lock();
	}
}

int main(){
	while(1) { __CPROVER_ASYNC_1: TAS_backoff__main(); }
}
