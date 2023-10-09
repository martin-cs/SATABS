void *malloc(unsigned s);
_Bool nondet_bool();

int main()
{
  int *p;
  int x;
  
  p=malloc(100*sizeof(int));
  
  if(nondet_bool()) p=&x;
  
  (*p)++;
}
