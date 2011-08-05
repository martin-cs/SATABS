#define NULL ((void *)0)

int main()
{
  int *p, *q;
  int x, y, z;
  char ch;
  
  p=&x;
  q=p;
  
  if(z)
    q=(int *)&ch;
  
  y=*q;
}
