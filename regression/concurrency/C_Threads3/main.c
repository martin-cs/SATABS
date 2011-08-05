int g;

void __CPROVER_atomic_begin();
void __CPROVER_atomic_end();

void t()
{
  // this is atomic!
  
  __CPROVER_atomic_begin();
  g=2;
  g=1;
  __CPROVER_atomic_end();
}

int main()
{
  g=1;

  __CPROVER_ASYNC_1: t();
  
  assert(g==1);
}
