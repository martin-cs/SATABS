int x = 0;
int done1 = 0;

int main()
{
  int y = 0;
  x = y;

  __CPROVER_ASYNC_01: x = x + 1, done1 = 1;
  x = x + 2;
  __CPROVER_assume(done1);
  
  x = x;
  y = y;
  
  assert(x == 3); //VS
  assert(y == 0); //VS
  assert(x == y + 3); //VF
}
