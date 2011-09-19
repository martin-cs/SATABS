//original file: EBStack.java
//amino-cbbs\trunk\amino\java\src\main\java\org\amino\ds\lockfree
//push only

#ifdef USE_BRANCHING_ASSUMES
#define bassume(e) __CPROVER_assume(e)
#else
#define bassume(e)
#endif

#ifdef SATABS
#define assume(e) __CPROVER_assume(e)

#define acquire(m) \
{ \
  __CPROVER_atomic_begin(); \
	__CPROVER_assume(m==0); \
	m = 1; \
	__CPROVER_atomic_end(); \
}
#define release(m) \
{ \
  __CPROVER_atomic_begin(); \
	__CPROVER_assume(m==1); \
	m = 0; \
	__CPROVER_atomic_end(); \
}
#endif

#ifdef SATABS
#define atomic_assert(e) assert(e)
#else
int m = 0;
#define atomic_assert(e) {acquire(m);assert(e);release(m);}
#endif

#define WORDT_NULL 0
typedef int WORDT;
typedef int SIZET;
typedef int WORDT_Ptr;
typedef int WORDT_Ptr_Ptr;
typedef int E;

#define MEMSIZE (2*32+1) //0 for "NULL"
WORDT memory[MEMSIZE];
#define INDIR(cell,idx) memory[cell+idx]

SIZET next_alloc_idx = 1;
int m = 0;
volatile WORDT_Ptr top;

inline WORDT_Ptr index_malloc(){
	SIZET curr_alloc_idx = -1;

	acquire(m);
	if(next_alloc_idx+2-1 > MEMSIZE){
		bassume(next_alloc_idx+2-1 > MEMSIZE);
		release(m);
		curr_alloc_idx = WORDT_NULL;
	}else{
		bassume(!(next_alloc_idx+2-1 > MEMSIZE));
		curr_alloc_idx = next_alloc_idx;
		next_alloc_idx += 2;
		release(m);
	}

	return curr_alloc_idx;
}

inline void EBStack_init(){
	top = WORDT_NULL;
}

inline int isEmpty() {
	return top == WORDT_NULL;
}

inline int push(E d) {
	WORDT_Ptr oldTop = -1, newTop = -1;

	newTop = index_malloc();
	if(newTop == WORDT_NULL){
		bassume(newTop == WORDT_NULL);
		return 0;
	}else{
		bassume(!(newTop == WORDT_NULL));
		INDIR(newTop,0) = d;

		acquire(m);
		oldTop = top;
		INDIR(newTop,1) = oldTop;
		top = newTop; 
		release(m);
		return 1;
	}
}

inline void init(){
	EBStack_init();
}

inline void push_loop(){
	int r = -1;
	int arg = rand();
	while(1){
		r = push(arg);
		atomic_assert(!r || !isEmpty());
	}
}

int m2 = 0;
#define STATE_UNINITIALIZED	0
#define STATE_INITIALIZED	1

volatile int state = STATE_UNINITIALIZED;
void thr1()
{
	acquire(m2);
	switch(state)
	{
	case STATE_UNINITIALIZED: 
		EBStack_init();
		state = STATE_INITIALIZED;
		//fall-through
	case STATE_INITIALIZED: 
		release(m2);
		
		push_loop();
		break;
	}
}

int main()
{
	while(1) { __CPROVER_ASYNC_01: thr1(); }
}
