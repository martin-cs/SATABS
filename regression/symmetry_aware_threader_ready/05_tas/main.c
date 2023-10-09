//Simple test_and_set lock with exponential backoff
//
//From Algorithms for Scalable Synchronization on Shared-Memory Multiprocessors, 1991 (Fig. 1).
//Also available as pseudo-code here: http://www.cs.rochester.edu/research/synchronization/pseudocode/ss.html#tas

#ifdef USE_BRANCHING_ASSUMES
#define bassume(e) __CPROVER_assume(e)
#else
#define bassume(e)
#endif

#ifdef SATABS
#define assume(e) __CPROVER_assume(e)
#endif

#define unlocked 0
#define locked 1
volatile int lock = unlocked;

#ifdef SATABS
#define TAS(v,o) \
{ \
	__CPROVER_atomic_begin(); \
	o = v; \
	v = 1; \
	__CPROVER_atomic_end(); \
}
#else
#define TAS(v,o) \
{ __blockattribute__((atomic)) \
	o = v; \
	v = 1; \
}
#endif

inline void acquire_lock(){
	int delay;
	int cond;

	delay = 1;
	TAS(lock,cond);
	while(cond == locked){
		bassume(cond == locked);
		pause(delay);
		if(delay*2 > delay) 
			delay *= 2;
		TAS(lock,cond);
	}
	bassume(!(cond == locked));
	assert(cond != lock);
}

inline void release_lock(){
	assert(lock != unlocked);
	lock = unlocked; 
}

int c = 0;
void thr1(){
	while(1){
		acquire_lock();
		c++; assert(c == 1); c--;
		release_lock();
	}
}

int main(){
	while(1) { __CPROVER_ASYNC_1: thr1(); }
}
