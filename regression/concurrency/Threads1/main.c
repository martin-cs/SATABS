int g;

void t1()
{
  g=1;
}

void t2()
{
  g=2;
}

int main()
{
  __CPROVER_ASYNC_1: t1();
  __CPROVER_ASYNC_2: t2();
  
  assert(g==0 || g==2);
}
