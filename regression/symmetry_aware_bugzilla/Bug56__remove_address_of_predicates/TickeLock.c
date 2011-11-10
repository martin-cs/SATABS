//Ticket lock with proportional backoff
//
//From Algorithms for Scalable Synchronization on Shared-Memory Multiprocessors, 1991 (Fig. 2).
//Also available as pseudo-code here: http://www.cs.rochester.edu/research/synchronization/pseudocode/ss.html#ticket

//satabs ./TickeLock.c ./basics.c --iterations 50 -DSATABS --max-cube-length 2 --modelchecker boom --save-bps --full-inlining --v 9 --max-threads 2 --function main -DSIMPL 2>/dev/null
//Time: 143.011 total, 140.517 abstractor, 1.539 model checker, 0.002 simulator, 0.942 refiner
//Iterations: 3
//Predicates: 28
//VERIFICATION SUCCESSFUL

//with --max-cube-length 3 it takes too long
//boom ./satabs.3.bp --por ample-bcst --no-stats --threadbound 3 -> V.F., as expected due to the counter

//13:50 09/01/2011 added SIMPL wrap around, since then Satabs has problems verifying it. 

#include "basics.h"

struct lock_t{
      unsigned next_ticket;
      unsigned now_serving;
} volatile lock = {0,0};

unsigned fetch_and_increment__next_ticket(){
	unsigned value;
	PRETPREDS
	PREDICATE(value == lock.next_ticket); PREDICATE(value == 0); PREDICATE(value == 1); PREDICATE(value == 2);
	atomic_begin();
		value = lock.next_ticket;
		lock.next_ticket++;
	atomic_end();
    return value;
}

void acquire_lock(){
	unsigned my_ticket; 
	my_ticket = fetch_and_increment__next_ticket(); 
	PREDICATE(my_ticket == 0); PREDICATE(my_ticket == 1); PREDICATE(my_ticket == 2);
	PREDICATE(lock.now_serving == my_ticket);
	//returns old value; arithmetic overflow is harmless
	while(1){
		pause(my_ticket - lock.now_serving);
		// consume this many units of time
		// on most machines, subtraction works correctly despite overflow
		if(lock.now_serving == my_ticket)
			return;
	}
}
  
void release_lock(){
	lock.now_serving++;
}

int c = 0;
void TicketLock__main(){
	PREDICATE(c == 0); PREDICATE(c == 1);
	acquire_lock();
	c++;assert(c == 1);c--;
	release_lock();
}

#ifdef SATABS
int main(){
	PREDICATE(lock.now_serving == 0); PREDICATE(lock.now_serving == 1); PREDICATE(lock.now_serving == 2);
	PREDICATE(lock.next_ticket == 0); PREDICATE(lock.next_ticket == 1); PREDICATE(lock.next_ticket == 2);
	while(1) __CPROVER_ASYNC_1: TicketLock__main();
}
#endif
