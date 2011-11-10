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

#define WORKPERTHREAD 2
#define THREADSMAX 3
volatile int max = 0x80000000;

int storage[WORKPERTHREAD*THREADSMAX];

#ifdef SATABS
#define CAS(v,e,u,r) \
{ \
	/*__CPROVER_atomic_begin();*/ \
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
	/*__CPROVER_atomic_end();*/ \
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

inline void findMax(int offset){
	int i;
	int e;
	int c; 
	int cret;

	for(i = offset; i < offset+WORKPERTHREAD; i++) {
#ifdef BUG
		e = storage[i];
#else
    e = rand();
#endif

		while(1){
			c = max;
			if(e > c){
				bassume(e > c);
				CAS(max,c,e,cret);
				if(cret){
					bassume(cret);
					break;
				}else{
					bassume(!(cret));
				}
			}else{
				bassume(!(e > c));
				break;
			}
		}

		assert(e <= max);
	}
}

void thr1() {
	int offset;

#ifdef SATABS
	assume(offset % WORKPERTHREAD == 0 && offset >= 0 && offset < WORKPERTHREAD*THREADSMAX);
#else
	assume(offset < WORKPERTHREAD && offset >= 0 && offset < WORKPERTHREAD*THREADSMAX);
#endif

	findMax(offset);
}

int main(){
	while(1) { __CPROVER_ASYNC_01: thr1(); }
}
