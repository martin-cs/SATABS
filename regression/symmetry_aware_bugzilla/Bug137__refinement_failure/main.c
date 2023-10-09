int m = 0, seed = 0;
int f(int n) {
	int r, p;
#ifdef NOBUG
	__CPROVER_parameter_predicates();
#endif
	__CPROVER_atomic_begin();
	__CPROVER_assume(m==0);
	m = 1;
	__CPROVER_atomic_end();
	r = seed;
	do n = rand(); while(n == r);
	seed = n;
	__CPROVER_atomic_begin();
	__CPROVER_assume(m==1);
	m = 0;
	__CPROVER_atomic_end();
	p = n % n;
	assert(p <= 10);
	return p;
}

int main(){ while(1) { __CPROVER_ASYNC_01: f(10); }}
