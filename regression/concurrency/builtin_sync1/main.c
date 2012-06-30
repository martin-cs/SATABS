int g;
_Bool mutex;

void t1()
{
  while(!__sync_bool_compare_and_swap(&g, 0, 1));

  assert(!mutex);
  assert(g==1);
  mutex=1;
}

void t2()
{
  while(__sync_val_compare_and_swap(&g, 0, 2)!=0);

  assert(!mutex);
  assert(g==2);
  mutex=1;
}

int main()
{
  __CPROVER_ASYNC_1: t1();
  __CPROVER_ASYNC_2: t2();
}
