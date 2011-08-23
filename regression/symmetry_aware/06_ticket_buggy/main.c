//Simple test_and_set lock with exponential backoff
//
//From Algorithms for Scalable Synchronization on Shared-Memory Multiprocessors, 1991 (Fig. 1).
//Also available as pseudo-code here: http://www.cs.rochester.edu/research/synchronization/pseudocode/ss.html#tas

#include "../basics.h"

struct lock_t{
	unsigned next_ticket;
	unsigned now_serving;
} volatile lock = {0,0};

#define FAILED 3 //this is already and the limit of what we can handle
#define NEXT(e) ((e + 1) % FAILED)

unsigned fetch_and_increment__next_ticket(){
	unsigned value;

#ifdef HPRED
	__CPROVER_return_predicates();
#endif

	atomic_begin();
	if(NEXT(lock.next_ticket) == lock.now_serving){ //we have to assure that (next_ticket + 1 != now_serving) to avoid non-mutual exclusive accesses
		assume(NEXT(lock.next_ticket) == lock.now_serving);
		atomic_end();
		value = FAILED;
	}else{
		assume(!(NEXT(lock.next_ticket) == lock.now_serving));
		value = lock.next_ticket;
		//lock.next_ticket++; 
		lock.next_ticket = NEXT(lock.next_ticket);
		atomic_end();
	}

	return value;
}

void acquire_lock(){
	unsigned my_ticket; 

	my_ticket = fetch_and_increment__next_ticket(); 
	//returns old value; arithmetic overflow is harmless (Alex: it is not if we have 2^64 threads)

	unsafe_assert(my_ticket != FAILED);
	if(my_ticket == FAILED){
		assume(my_ticket == FAILED);
		assume(0);
	}else{
		assume(!(my_ticket == FAILED));
		while(1){
			pause(my_ticket - lock.now_serving);
			// consume this many units of time
			// on most machines, subtraction works correctly despite overflow
			if(lock.now_serving == my_ticket){
				assume(lock.now_serving == my_ticket);
				break;
			}else{
				assume(!(lock.now_serving == my_ticket));
			}
		}
	}

	return;
}

void release_lock(){
	lock.now_serving++;
}

int c = 0;
void TicketLock__main(){
	acquire_lock();
	c++;
	assert(c == 1);
	c--;
	release_lock();
}

int main(){
#ifdef HPRED //removing any of them makes satabs discover ~30 predicates which it can then not abstract in reasonable time
	__CPROVER_predicate(lock.next_ticket == 0);
	__CPROVER_predicate(lock.next_ticket == 1);
	__CPROVER_predicate(lock.next_ticket == 2);
	__CPROVER_predicate(lock.next_ticket == 3);
	__CPROVER_predicate(lock.now_serving == 0);
	__CPROVER_predicate(lock.now_serving == 1);
	__CPROVER_predicate(lock.now_serving == 2);
	__CPROVER_predicate(lock.now_serving == 3);
#endif

	while(1) { __CPROVER_ASYNC_01: TicketLock__main(); }
}
