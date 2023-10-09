//original file: EBStack.java
//amino-cbbs\trunk\amino\java\src\main\java\org\amino\ds\lockfree
//push only
#include "../basics.h"

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

#if (TPRED >= 1)
#define APRED 1
#endif

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

#if (APRED >= 1)
	__CPROVER_predicate(curr_alloc_idx == 0);
#endif

	atomic_begin();
	if(next_alloc_idx+2-1 > MEMSIZE){
		assume(next_alloc_idx+2-1 > MEMSIZE);
		atomic_end();
		curr_alloc_idx = WORDT_NULL;
	}else{
		assume(!(next_alloc_idx+2-1 > MEMSIZE));
		curr_alloc_idx = next_alloc_idx;
		next_alloc_idx += 2;
		atomic_end();
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
	WORDT_Ptr chTop = -1;

#if (APRED >= 1)
	__CPROVER_predicate(s.top == 0);
	__CPROVER_predicate(newTop == 0);
	__CPROVER_predicate(s.top == oldTop);
#endif

	newTop = index_malloc();
	if(newTop == WORDT_NULL){
		assume(newTop == WORDT_NULL);
		return 0;
	}else{
		assume(!(newTop == WORDT_NULL));
		INDIR(newTop,0) = d;
		while (1) {
			oldTop = s.top;
			INDIR(newTop,1) = oldTop;
			//inlining of cas
			//atomic_begin();
			if (s.top == oldTop) {
				assume(s.top == oldTop);
				atomic_begin();
					chTop = s.top;
					s.top = newTop; 
				atomic_end();
				
				//atomic_end();
				
				unsafe_assert(chTop == oldTop);
				
				return 1;
			}else{
				assume(!(s.top == oldTop));
				//atomic_end();
			}
		}
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
	}
}

int main(){
	EBStack_init();
	while(1){ __CPROVER_ASYNC_01: thread_main(); }
}
