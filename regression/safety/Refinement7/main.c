struct S
{ 
  int i;
};

int main()
{
  struct S x1, x2, x3, x4;

  x1.i=1;

  x2=x1;
  x3=x2;
  x4=x3;

  assert(x4.i!=0);
}
