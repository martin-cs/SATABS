void f(_Bool flag)
{
  int local;
  
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
