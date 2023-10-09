void foo(unsigned int x, unsigned int y, unsigned int z) {
  int i, j, k;
  for(i=0; i<x; i++) {
    for(j=i+1; j<y; j++) {
      for(k = j; k < z; k++) {
	assert(k > i);
      }
    }
  }

  assert(i == x && (x == 0 || j == y || y <= x+1) && (x == 0 || y <= x+1 || k == z || z < y)) ;

}
