#ifdef SATABS
#define assume(e) __CPROVER_assume(e)
#endif

int t1=0, t2=0; // N natural-number tickets
int x; // variable to test mutual exclusion

thr1() {
  while (1) { 
    t1 = t2 + 1;

#ifdef SATABS
    assume(t1 < 10); //alex: the properties only holds for natural integers
#endif

    while( t1 >= t2 && ( t2 > 0 ) ) {}; // condition to exit the loop is (t1<t2 \/ t2=0)
    x=0;
    assert(x <= 0); //alex: with machine integers this property does not hold
    t1 = 0;
  }
}

thr2() {
  while (1) {
    t2 = t1 + 1;

#ifdef SATABS
    assume(t2 < 10); //alex: the properties only holds for natural integers
#endif

    while( t2 >= t1 && ( t1 > 0 ) ) {}; // condition to exit the loop is (t2<t1 \/ t1=0)
    x = 1;
    assert(x >= 1); //alex: with machine integers this property does not hold
    t2 = 0;
  }
}

#ifdef SATABS 
int main()
{
  __CPROVER_ASYNC_1: thr1();
  thr2();
}
#endif
