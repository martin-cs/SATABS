//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//Listing 2. A nonblocking counter using CAS

#ifdef USE_BRANCHING_ASSUMES
#define bassume(e) __CPROVER_assume(e)
#else
#define bassume(e)
#endif

#ifdef SATABS
#define assume(e) __CPROVER_assume(e)
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

volatile unsigned value;

unsigned thr1() {
	unsigned v,vn,casret;

	do {
		v = value;

		if(v == 0u-1) {
			bassume(v == 0u-1);
			return 0; 
		}else{
			bassume(!(v == 0u-1));
		}

		vn = v + 1;

		CAS(value,v,vn,casret);
	}
	while (casret==0);
	bassume(!(casret==0));
	assert(value > v); 

	return vn;
}

int main(){
	while(1) { __CPROVER_ASYNC_01: thr1(); }
}
