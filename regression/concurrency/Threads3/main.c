// this tests parameter passing

void f(int i)
{
  // this should hold
  __CPROVER_assert(i == 0, "Parameter correct");
}

int main()
{
  __CPROVER_ASYNC_1: f(0);
  f(0);
} 
