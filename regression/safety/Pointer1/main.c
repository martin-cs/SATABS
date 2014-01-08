int main()
{
  int *p, *q;
  int x, y, z;
  char ch;
  
  p=&x;
  q=p;
  
  if(z)
    q=(int *)&ch;

  // this is a type violation if z is true  
  y=*q;
}
