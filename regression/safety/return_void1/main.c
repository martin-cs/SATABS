#include <assert.h>

int g;

void f()
{
  return;
  g=1;
}

int main()
{
  f();
  assert(g==0);
}
