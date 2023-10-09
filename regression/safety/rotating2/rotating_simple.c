
int foo() {

	int a, b, c, i, temp, res, j, x;
	
    a = 1;
    b = 2;
    c = 3;
	
	x = 0;

  for(i=0; i<100; i++) {
		assert(a != b);
		temp = a;
		a = b;
		b = c;
		c = temp;
  }

  assert(x == 0);
}
