int main()
{
  int i, j;
  
  i=-1;
  
  __CPROVER_assume(i==2);

  j=3;
  // this should pass
  assert(j>=0);
}
