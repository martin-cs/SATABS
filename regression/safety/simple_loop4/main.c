void foo(int i) {
  
  int j, k;

  __CPROVER_assume(i>=0 && i < 10);
  
  for(j=i+1; j<10; j++) {
    for(k=j+1; k<12; k++) {
      assert(k > i);
    }
  }
  
}
