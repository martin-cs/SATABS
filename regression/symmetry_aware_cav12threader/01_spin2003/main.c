#ifdef SATABS
#define assert(e) __CPROVER_assert(e,"error")

#define acquire(m) \
{ \
  __CPROVER_atomic_begin(); \
	__CPROVER_assume(m==0); \
	m = 1; \
	__CPROVER_atomic_end(); \
} \

#define release(m) \
{ \
  __CPROVER_atomic_begin(); \
	__CPROVER_assume(m==1); \
	m = 0; \
	__CPROVER_atomic_end(); \
} \

#endif

int x=1, m=0;

void thr() {
  acquire(m); // m=0 /\ m'=1
  x = 0;
  x = 1;
  assert(x>=1);
  release(m);
}

#ifdef SATABS 
int main()
{
  while(1) __CPROVER_ASYNC_1:	 thr();
}
#endif
