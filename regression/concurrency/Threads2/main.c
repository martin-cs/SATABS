int g;

void t1()
{
  g=2;
}

int main()
{
  g=1;
  
  assert(g==1);

  __CPROVER_ASYNC_1: t1();
}
