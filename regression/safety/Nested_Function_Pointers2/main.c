void start(
  void *(*__start_routine) (void *),
  void *__arg)
{
  CPROVER_ASYNC_1: __start_routine(__arg);
}

unsigned nicefun(int a, int b)
{
  // should fail
  assert(0);
}

void *fun(void* p)
{
  int i;
  i=1;
  (* (unsigned (*)(int, int)) p) (0,0);
  i=2;
}

int main(void)
{
  start(&fun, &nicefun);
}


