#ifdef SATABS
#define assume(e) __CPROVER_assume(e)
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

#define WORKPERTHREAD 2
#define THREADSMAX 3
volatile int max = 0x80000000;

int storage[WORKPERTHREAD*THREADSMAX];

inline void findMax(int offset){
	int i;
	int e;
	int my_max = 0x80000000;
	int c; 
	int cret;

	for(i = offset; i < offset+WORKPERTHREAD; i++) {
#ifndef NOBUG
		e = storage[i];
#else
    e = rand();
#endif

		if(e > my_max) {
			bassume(e > my_max);
			my_max = e;
		}else{
			bassume(!(e > my_max));
		}
		assert(e <= my_max);
	}

	while(1){
		c = max;
		if(my_max > c){
			bassume(my_max > c);
			 CAS(max,c,my_max,cret);
			if(cret){
				bassume(cret);
				break;
			}else{
				bassume(!(cret));
			}
		}else{
			bassume(!(my_max > c));
			break;
		}
	}

	assert(my_max <= max);
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
