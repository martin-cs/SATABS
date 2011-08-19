//Ticket lock with proportional backoff
//
//From Algorithms for Scalable Synchronization on Shared-Memory Multiprocessors, 1991 (Fig. 2).
//Also available as pseudo-code here: http://www.cs.rochester.edu/research/synchronization/pseudocode/ss.html#ticket

struct lock_t{
	unsigned next_ticket;
	unsigned now_serving;
} volatile lock = {0,0};

#define FAILED 3 //this is already and the limit of what we can handle
#define NEXT(e) ((e + 1) % FAILED)

unsigned fetch_and_increment__next_ticket(){
	unsigned value;

	__CPROVER_return_predicates();
	__CPROVER_atomic_begin();
	if(NEXT(lock.next_ticket) == lock.now_serving){ 
		__CPROVER_assume(NEXT(lock.next_ticket) == lock.now_serving);
		__CPROVER_atomic_end();
		value = FAILED;
	}else{
		__CPROVER_assume(!(NEXT(lock.next_ticket) == lock.now_serving));
		value = lock.next_ticket;
		//lock.next_ticket++; 
		lock.next_ticket = NEXT(lock.next_ticket);
		__CPROVER_atomic_end();
	}

	return value;
}

void acquire_lock(){
	unsigned my_ticket; 

	my_ticket = fetch_and_increment__next_ticket(); 
	//returns old value; arithmetic overflow is harmless (Alex: it is not if we have 2^64 threads)

	if(my_ticket == FAILED){
		__CPROVER_assume(my_ticket == FAILED);
		__CPROVER_assume(0);
	}else{
		__CPROVER_assume(!(my_ticket == FAILED));
		while(1){
			pause(my_ticket - lock.now_serving);
			// consume this many units of time
			// on most machines, subtraction works correctly despite overflow
			if(lock.now_serving == my_ticket){
				__CPROVER_assume(lock.now_serving == my_ticket);
				break;
			}else{
				__CPROVER_assume(!(lock.now_serving == my_ticket));
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
	__CPROVER_predicate(lock.next_ticket == 0);
	__CPROVER_predicate(lock.next_ticket == 1);
	__CPROVER_predicate(lock.next_ticket == 2);
	__CPROVER_predicate(lock.next_ticket == 3);
	__CPROVER_predicate(lock.now_serving == 0);
	__CPROVER_predicate(lock.now_serving == 1);
	__CPROVER_predicate(lock.now_serving == 2);
	__CPROVER_predicate(lock.now_serving == 3);

	while(1) { __CPROVER_ASYNC_01: TicketLock__main(); }
}
