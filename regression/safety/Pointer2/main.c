#define NULL ((void *)0)

struct S
{
  int *p;
};

int main()
{
  struct S s;
  int *p;
  int y;
  int z;
  
  s.p=&z;
  
  y=*s.p;
}
