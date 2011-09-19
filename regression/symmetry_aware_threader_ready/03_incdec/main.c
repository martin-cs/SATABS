//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//Listing 2. A counter using locks

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

volatile unsigned value = 0, m = 0;

/*helpers for the property*/
volatile unsigned inc_flag = 0;
volatile unsigned dec_flag = 0;

inline unsigned inc() {
	unsigned inc_v = 0;

	acquire(m);
	if(value == 0u-1) {
#ifdef USE_BRANCHING_ASSUMES
		assume(value == 0u-1);
#endif
		release(m);

		return 0;
	}else{
#ifdef USE_BRANCHING_ASSUMES
		assume(!(value == 0u-1));
#endif

		inc_v = value;
		inc_flag = 1, value = inc_v + 1; /*set flag, then update*/
		release(m);

		atomic_assert(dec_flag || value > inc_v);

		return inc_v + 1;
	}
}

inline unsigned dec() {
	unsigned dec_v;

	acquire(m);
	if(value == 0) {
#ifdef USE_BRANCHING_ASSUMES
		assume(value == 0);
#endif
		release(m);

		return 0u-1; /*decrement failed, return max*/
	}else{
#ifdef USE_BRANCHING_ASSUMES
		assume(!(value == 0));
#endif

		dec_v = value;
		dec_flag = 1, value = dec_v - 1; /*set flag, then update*/
		release(m);

		atomic_assert(inc_flag || value < dec_v);

		return dec_v - 1;
	}
}

void thr1(){
	int r = -1;
	r = rand();

	if(r){ inc(); }
	else{ dec(); }
}

int main(){
	while(1) { __CPROVER_ASYNC_01: thr1(); }
}
