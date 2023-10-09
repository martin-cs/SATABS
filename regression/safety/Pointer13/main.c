#include <stdlib.h>

int main()
{
  int x, y, *p, *q, job;
  
  switch(job)
  {
  case 0:
    x=1;
    assert(x==1);
    break;
    
  case 1:
    p=&x;
    *p=10;
    assert(x==10);
    break;
    
  case 2:
    p=&x;
    q=p;
    *q=20;
    assert(*p==20);
    break;
  
  case 3:
    p=&x;
    x=1;
    p++;
    p--;
    assert(*p==1);
    break;
    
  case 4:
    y=4;
    p=&x;
    *p=3;
    assert(y==4);
    break;
    
  case 5:
    p=(int *)malloc(sizeof(int));
    q=(int *)malloc(sizeof(int));
    *p=123;
    *q=455;
    assert(*p==123);
  }
}
