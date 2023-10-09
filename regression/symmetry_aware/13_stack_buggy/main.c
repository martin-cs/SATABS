//original file: EBStack.java
//amino-cbbs\trunk\amino\java\src\main\java\org\amino\ds\lockfree
//push only
#define WORDT_NULL 0
typedef int WORDT;
typedef int SIZET;
typedef int WORDT_Ptr;
typedef int WORDT_Ptr_Ptr;
typedef int E;

struct Node {
	volatile E data;
	volatile WORDT_Ptr next;
};

#define MEMSIZE (2*32+1) //0 for "NULL"
WORDT memory[MEMSIZE];
#define INDIR(cell,idx) memory[cell+idx]

SIZET next_alloc_idx = 1;

struct EBStack {
	volatile WORDT_Ptr top;
};

struct EBStack s;

WORDT_Ptr index_malloc(){
	SIZET curr_alloc_idx = -1;


	__CPROVER_atomic_begin();
	if(next_alloc_idx+2-1 > MEMSIZE){
#ifdef USE_BRANCHING_ASSUMES
		__CPROVER_assume(next_alloc_idx+2-1 > MEMSIZE);
#endif
		__CPROVER_atomic_end();
		curr_alloc_idx = WORDT_NULL;
	}else{
#ifdef USE_BRANCHING_ASSUMES
		__CPROVER_assume(!(next_alloc_idx+2-1 > MEMSIZE));
#endif
		curr_alloc_idx = next_alloc_idx;
		next_alloc_idx += 2;
		__CPROVER_atomic_end();
	}

	return curr_alloc_idx;
}

void EBStack_init(){
	s.top = WORDT_NULL;
}

int isEmpty() {
	return s.top == WORDT_NULL;
}

int push(E d) {
	WORDT_Ptr oldTop = -1, newTop = -1;

	newTop = index_malloc();
	if(newTop == WORDT_NULL){
#ifdef USE_BRANCHING_ASSUMES
		__CPROVER_assume(newTop == WORDT_NULL);
#endif
		return 0;
	}else{
#ifdef USE_BRANCHING_ASSUMES
		__CPROVER_assume(!(newTop == WORDT_NULL));
#endif
		INDIR(newTop,0) = d;

		//__CPROVER_atomic_begin();
		oldTop = s.top;
		INDIR(newTop,1) = oldTop;
		s.top = newTop; 
		//__CPROVER_atomic_end();
		return 1;
	}
}

void init(){
	EBStack_init();
}

void thread_main(){
	int r = -1;
	int arg = rand();
	while(1){
		r = push(arg);
		//assert(!r || !isEmpty());
		assert(!isEmpty());
	}
}

int main(){
	EBStack_init();
	while(1){ __CPROVER_ASYNC_01: thread_main(); }
}
