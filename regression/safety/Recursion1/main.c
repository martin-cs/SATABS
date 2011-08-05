int g;

_Bool nondet_bool();

void f()
{
  if(nondet_bool())
    f();

  // this should pass    
  assert(g==1);
}

int main()
{
  g=1;
  f();
}
