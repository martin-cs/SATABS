int main()
{
  unsigned int N, n;
  N=n;
  int arrayX[N], v;
  unsigned i, j;

  __CPROVER_assume(N>10 && N<200);
  
  arrayX[1]=1;
  
  if(i)
    arrayX[1]=2;

  if(i)
    assert(arrayX[1]==2);
}
