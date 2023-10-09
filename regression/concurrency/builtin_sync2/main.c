int g;
_Bool f1, f2;

void t1()
{
  __sync_fetch_and_add(&g, 1);
  f1=1;
}

void t2()
{
  __sync_fetch_and_add(&g, 1);
  f2=1;
}

int main()
{
  __CPROVER_ASYNC_1: t1();
  __CPROVER_ASYNC_2: t2();

  // two atomic increments produce the sum 2  
  if(f1 && f2)
    assert(g==2);
}
