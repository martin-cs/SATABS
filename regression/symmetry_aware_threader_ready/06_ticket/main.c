//Ticket lock with proportional backoff
//
//From Algorithms for Scalable Synchronization on Shared-Memory Multiprocessors, 1991 (Fig. 2).
//Also available as pseudo-code here: http://www.cs.rochester.edu/research/synchronization/pseudocode/ss.html#ticket

#ifdef USE_BRANCHING_ASSUMES
#define bassume(e) __CPROVER_assume(e)
#else
#define bassume(e)
#endif

#ifdef HPRED
#define hpredicate(e) __CPROVER_predicate(e)
#define ppredicate(e) __CPROVER_return_predicates(e)
#else
#define hpredicate(e)
#define ppredicate(e)
#endif

#ifdef SATABS
#define assume(e) __CPROVER_assume(e)
#endif

volatile unsigned next_ticket = 0;
volatile unsigned now_serving = 0;

#define FAILED 3 //this is already and the limit of what we can handle

#ifdef SATABS
#define NEXT(e) ((e + 1) % FAILED)
#else
#define NEXT(e) ((e+1 == FAILED)?0:e+1)
#endif

inline unsigned fetch_and_increment__next_ticket(){
	unsigned value;

	ppredicate();
#ifdef SATABS
	{ __CPROVER_atomic_begin();
#else
	{ __blockattribute__((atomic))
#endif
		if(NEXT(next_ticket) == now_serving){ 
			bassume(NEXT(next_ticket) == now_serving);
			value = FAILED;
		}
		else
		{
			bassume(!(NEXT(next_ticket) == now_serving));
			value = next_ticket;
			next_ticket = NEXT(next_ticket);
		}
		
#ifdef SATABS
	__CPROVER_atomic_end(); }
#else
	}
#endif

	return value;
}

inline void acquire_lock(){
	unsigned my_ticket; 

	my_ticket = fetch_and_increment__next_ticket(); //returns old value; arithmetic overflow is harmless (Alex: it is not if we have 2^64 threads)

	if(my_ticket == FAILED){
		bassume(my_ticket == FAILED);
		assume(0);
	}else{
		bassume(!(my_ticket == FAILED));
		while(1){
			pause(my_ticket - now_serving);
			// consume this many units of time
			// on most machines, subtraction works correctly despite overflow
			if(now_serving == my_ticket){
				bassume(now_serving == my_ticket);
				break;
			}else{
				bassume(!(now_serving == my_ticket));
			}
		}
	}

	return;
}

inline void release_lock(){
	now_serving++;
}

int c = 0;
void thr1(){
	acquire_lock();
	c++;
	assert(c == 1);
	c--;
	release_lock();
}

int main(){
	hpredicate(next_ticket == 0);
	hpredicate(next_ticket == 1);
	hpredicate(next_ticket == 2);
	hpredicate(next_ticket == 3);
	hpredicate(now_serving == 0);
	hpredicate(now_serving == 1);
	hpredicate(now_serving == 2);
	hpredicate(now_serving == 3);
	while(1) { __CPROVER_ASYNC_01: thr1(); }
}
