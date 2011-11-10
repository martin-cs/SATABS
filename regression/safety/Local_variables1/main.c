void f(_Bool flag)
{
  int local;
#ifdef FIX
  int x;
  local=x;
#endif
  
  if(flag)
    assert(local==123); // this should fail
  else
    local=123;
}

int main()
{
  f(0);
  f(1);
}
