unsigned m=0, max=0;

void f(){
	unsigned e;		
	__CPROVER_atomic_begin();
	__CPROVER_assume(m==0);
#ifdef NOBUG
	__CPROVER_predicate(m==0);
#endif
	m = 1;
	__CPROVER_atomic_end();

	if(e > max) max = e;

	__CPROVER_atomic_begin();
	__CPROVER_assume(m==1);
	m = 0;
	__CPROVER_atomic_end();

	assert(e <= max);
}

int main(){ while(1) { __CPROVER_ASYNC_01: f(); } }