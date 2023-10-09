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
#define atomic_assert(e) assert(e)
#else
int m = 0;
#define atomic_assert(e) {acquire(m);assert(e);release(m);}
#endif

#ifdef SATABS
#define CAS(v,e,u,r,flag) \
{ \
	__CPROVER_atomic_begin(); \
	if(v == e) \
	{ \
		bassume(v == e); \
		flag = 1, v = u, r = 1; \
	} \
	else \
	{ \
		bassume(!(v == e)); \
		r = 0; \
	} \
	__CPROVER_atomic_end(); \
}
#else
#define CAS(v,e,u,r,flag) \
{ __blockattribute__((atomic)) \
	if(v == e) \
	{ \
		flag = 1, v = u, r = 1; \
	} \
	else \
	{ \
		r = 0; \
	} \
}
#endif

volatile unsigned value = 0;

/*helpers for the property*/
volatile unsigned inc_flag = 0;
volatile unsigned dec_flag = 0;

inline unsigned inc() {
	unsigned inc__v, inc__vn, inc__casret;

	do {
		inc__v = value;

		if(inc__v == 0u-1) {
			bassume(inc__v == 0u-1);
			return 0; /*increment failed, return min*/
		}else{
			bassume(!(inc__v == 0u-1));
		}

		inc__vn = inc__v + 1;

		CAS(value,inc__v,inc__vn,inc__casret,inc_flag);
	}
	while (inc__casret==0);
	bassume(!(inc__casret==0));

	atomic_assert(dec_flag || value > inc__v);

	return inc__vn;
}

inline unsigned dec() {
	unsigned dec__v, dec__vn, dec__casret;

	do {
		dec__v = value;

		if(dec__v == 0) {
			bassume(dec__v == 0);
			return 0u-1; /*decrement failed, return max*/
		}else{
			bassume(!(dec__v == 0));
		}

		dec__vn = dec__v - 1;

		CAS(value,dec__v,dec__vn,dec__casret,dec_flag);

	}
	while (dec__casret==0);
	bassume(!(dec__casret==0));

	atomic_assert(inc_flag || value < dec__v);
	return dec__vn;
}

void thr1(){
	int r = -1;
	r = rand();

	if(r){ inc(); }
	else{ dec(); }
}

int main(){
	while(1) { 
		__CPROVER_ASYNC_01: thr1();
	}
}
