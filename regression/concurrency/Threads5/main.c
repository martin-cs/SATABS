int g;

void f1(void)
{
  // this should pass
  __CPROVER_assert(g==1, "assertion in f1");
  g=2;
}

void callp(void (*func)(void))
{
  __CPROVER_ASYNC_1: func();
}

int main(){
  g=1;
  callp(f1);
}

