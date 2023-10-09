int nondet();


int foo() {
  int i, a, b, c, res, temp;
  
  a = 1;
  b = 2;
  c = 3;

  for(i=0; i<100; ) {
    res = nondet();
    __CPROVER_assume(res == 0 || res == 1);
    if(res) {
      assert(a!=b);
      temp = a;
      a = b;
      b = c;
      c = temp;
      i++;
    }
  }

}
