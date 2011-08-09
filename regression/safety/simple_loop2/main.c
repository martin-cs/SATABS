void foo(int x, int y) {
  int i, j, k;
  for(i=0; i<x; i++) {
    for(j=i+1; j<y; j++) {
	assert(j > i);
    }
  }

}
