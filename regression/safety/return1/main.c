#include <assert.h>

// there is no body for foo(), deliberately.
int foo();

int bar()
{
  int a;
  a = 0 + foo();
  return a;
}

int main(){
  int x,y;
  x = bar();
  y = bar();
  // this should fail,
  // as foo() returns something that is nondeterministically chosen
  assert(x == y);
}
