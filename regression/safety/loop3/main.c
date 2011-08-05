main(){
  unsigned i,j,n;
  int x[n];
  
  __CPROVER_assume(n<100000);
  
  for(
    i=0;
    i<n;
    i=i+2)
  {
    x[i]=0;
  }
}
