//http://www.ibm.com/developerworks/java/library/j-jtp11234/
//Listing 5. Implementing a thread-safe PRNG with synchronization and atomic variables

#ifdef USE_BRANCHING_ASSUMES
#define bassume(e) __CPROVER_assume(e)
#else
#define bassume(e)
#endif

#ifdef HPRED
#define hpredicate(e) __CPROVER_predicate(e)
#define ppredicate(e) __CPROVER_parameter_predicates()
#define rpredicate(e) __CPROVER_return_predicates()
#else
#define hpredicate(e)
#define ppredicate(e)
#define rpredicate(e)
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

int m = 0;

inline int calculateNext(int s2){ 
	int calculateNext_return;
	ppredicate();

	do
	{
		calculateNext_return = rand();
	}
	while(calculateNext_return == s2 || calculateNext_return == 0);
	bassume(!(calculateNext_return == s2 || calculateNext_return == 0));

	return calculateNext_return;
}

volatile int seed; 

inline int PseudoRandomUsingAtomic_nextInt(int n) {
	int read, nexts, nextInt_return;

	hpredicate(n==10);
	acquire(m);
	read = seed;
	nexts = calculateNext(read);
	assert(nexts != read); 
	seed = nexts;
	release(m);
#ifdef SATABS
	nextInt_return = nexts % n;
#else
	assume(nexts < n + 1);
	nextInt_return = nexts;
#endif

	return nextInt_return;
}

inline void PseudoRandomUsingAtomic_monitor(){
	while(1)
	{
		assert(seed != 0);
	}
}

inline void PseudoRandomUsingAtomic_constructor(int init){
	seed = init;
}

inline void PseudoRandomUsingAtomic__threadmain(){ 
	int myrand;

	myrand = PseudoRandomUsingAtomic_nextInt(10);
	assert(myrand <= 10);
}

#define STATE_UNINITIALIZED	0
#define STATE_INITIALIZED	1

volatile int state = STATE_UNINITIALIZED;
void thr1()
{
	acquire(m);
	switch(state)
	{
	case STATE_UNINITIALIZED: 
		PseudoRandomUsingAtomic_constructor(1);
		state = STATE_INITIALIZED;
		release(m);
		
		PseudoRandomUsingAtomic_monitor(); //never returns
		break;
	case STATE_INITIALIZED: 
		release(m);
		
		PseudoRandomUsingAtomic__threadmain();
		break;
	}
}

int main()
{
	while(1) { __CPROVER_ASYNC_01: thr1(); }
}
