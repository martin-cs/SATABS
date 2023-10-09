int nondet();

int foo() {

	int a, b;
	int c, d, e, f, g, h, i, temp, res, j, x;
	
    a = 1;
    b = 2;
    c = 3;
    d = 4;
    e = 5;
	f = 6;
	g = 7;
	h = 8;
	
	x = 0;

  for(i=0; i<100; ) {

	  for(j=0; j < 100; j++)
	  {
		  assert(a != b);
		  temp = a;
		  a = b;
		  b = c;
		  c = d;
		  d = e;
		  e = f;
		  f = g;
		  g = h;
		  h = temp;
		  x = x;
	  }
      i++;
  }

	assert(x == 0);
}
