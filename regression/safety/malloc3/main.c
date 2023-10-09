void *malloc(unsigned s);

int main()
{
  int *p, *q, z;
  
  q=p=malloc(sizeof(int));
  
  *p=2;

//  p=malloc(sizeof(int));
  
//  *p=3;

  z=*q;
  
  assert(z==2);
}
