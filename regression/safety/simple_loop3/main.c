void foo(int x) {
  int i, j, k;
  for(i=0; i<20; i++) {
    for(j=i+1; j<1000; j++) {
      for(k=j+1; k<2000; k++) {
		  assert(k > j);
      }
    }
  }

}
