int g;

void t1()
{
  g=1;
}

void t2()
{
  g=2;
}

void create_thread(void (*t)())
{
  __CPROVER_ASYNC_1: t();
}

int main()
{
  create_thread(t1);
  create_thread(t2);
  
  assert(g==0);
}
