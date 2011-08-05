
typedef struct _S { unsigned a; unsigned b; } S;

int main(void)
{
  S interface;
  unsigned i=0;

  while(i<interface.a)
  {
    interface.b=2;
    i++;
  }

  return 0;
}
