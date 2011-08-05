void f1(void)
{
}

void callp(void (*func)(void)){
  // this tests the alias analysis for *func
  // bug: "unexpected target function"
  __CPROVER_ASYNC_1: func();
}

int main()
{
  // call twice!
  callp(f1);
  callp(f1);
}

