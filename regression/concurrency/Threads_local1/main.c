__CPROVER_thread_local _Bool local_flag1;

void t1()
{
  // this should be safe, as the flag is thread-local
  local_flag1=0;
  local_flag1=1;
  assert(local_flag1);

  // this should be safe, as the flag is thread-local
  _Bool local_flag2;
  local_flag2=0;
  local_flag2=1;
  assert(local_flag2);
}

int main()
{
  __CPROVER_ASYNC_1: t1();
  
  t1();
}
