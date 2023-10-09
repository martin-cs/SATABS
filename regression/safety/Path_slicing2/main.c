struct X
{
  int i;
  int j;
};

int main()
{
  struct X y;
  y.i=1;
  y.j=2;

  struct X x=y;

  // should hold
  assert(x.i!=0);
}
