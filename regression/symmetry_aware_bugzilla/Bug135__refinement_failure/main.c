#ifdef NOBUG1
volatile int max = 0, m = 0;
#else
volatile int max = 0x80000000, m = 0;
#endif

void main()
{
#ifdef NOBUG2
	int e;
#else
	int e;
	e = rand();
#endif
  {
    if(e > max) {
      __CPROVER_assume(e > max);
      max = e;
    }else{
      __CPROVER_assume(!(e > max));
    }
  }
  assert(e == max);
}
