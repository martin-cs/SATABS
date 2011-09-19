//http://www.ibm.com/developerworks/java/library/j-jtp11234/
//Listing 5. Implementing a thread-safe PRNG with synchronization and atomic variables

#ifdef SATABS
#define assume(e) __CPROVER_assume(e)
#endif

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

#ifdef SATABS
#define CAS(v,e,u,r) \
{ \
	__CPROVER_atomic_begin(); \
	if(v == e) \
	{ \
		bassume(v == e); \
		v = u, r = 1; \
	} \
	else \
	{ \
		bassume(!(v == e)); \
		r = 0; \
	} \
	__CPROVER_atomic_end(); \
}
#else
#define CAS(v,e,u,r) \
{ __blockattribute__((atomic)) \
	if(v == e) \
	{ \
		v = u, r = 1; \
	} \
	else \
	{ \
		r = 0; \
	} \
}
#endif

inline int PseudoRandomUsingAtomic_nextInt(int n)
{
	int read, nexts, casret, nextInt_return;
	ppredicate(n==10);

	while(1) {
		read = seed;
		nexts = calculateNext(read);
		assert(nexts != read); 
		CAS(seed,read,nexts,casret);

		if(casret == 1){
			bassume(casret == 1);
#ifdef SATABS
			nextInt_return = nexts % n;
#else
			assume(nexts < n);
			nextInt_return = nexts;
#endif
			break;
		}else{
			bassume(!(casret == 1));
		}
	}

	return nextInt_return;
}

inline void PseudoRandomUsingAtomic_monitor()
{
	while(1)
	{
		assert(seed != 0);
	}
}

inline void PseudoRandomUsingAtomic_constructor(int init)
{
	seed = init;
}

inline void PseudoRandomUsingAtomic__threadmain()
{ 
	int myrand;

	myrand = PseudoRandomUsingAtomic_nextInt(10);
	assert(myrand <= 10);
}

int m = 0;
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
