#include <assert.h>

int nondet();

int main() {
  int a, b, c, d, e, i, temp, res;
  
  a = 1;
  b = 2;
  c = 3;
  d = 4;
  e = 5;

  for(i=0; i<100; ) {
    res = nondet();
    __CPROVER_assume(res == 0 || res == 1);
    if(res) {
      assert(a != b);
      temp = a;
      a = b;
      b = c;
      c = d;
      d = e;
      e = temp;
      i++;
    }
  }

}
