#define MEMSIZE (2*2+1) //0 is reserved
int memory[MEMSIZE];
int next_alloc_idx = 1; //0 is reserved for 0

int alloc(){
	int curr_alloc_idx
#ifdef NOBUG
	 = -1
#endif
  ;
	
	__CPROVER_atomic_begin();
	if(next_alloc_idx+2-1 > MEMSIZE){
		assume(next_alloc_idx+2-1 > MEMSIZE);
		__CPROVER_atomic_end();
		curr_alloc_idx = 0;
	}else{
		assume(!(next_alloc_idx+2-1 > MEMSIZE));
		curr_alloc_idx = next_alloc_idx;
		next_alloc_idx += 2;
		__CPROVER_atomic_end();
	}

  assert(curr_alloc_idx < MEMSIZE);
	return curr_alloc_idx;
}

int push(int d) {
	int newTop
#ifdef NOBUG
	 = -1
#endif
  ;
	newTop = alloc();
  assume(!(newTop == 0));
  assert(newTop < next_alloc_idx);
	return 1;
}

void thread_main(){
  while(1){
    push(1);
  }
}

int main(){
	while(1){ __CPROVER_ASYNC_01: thread_main(); }
}
