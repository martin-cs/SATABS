int g;

void f2()
{
  g=2;
}

void f()
{
  void (*q)();

  g=1;
  
  q=f2;
  
  q();
}

int main()
{
  void (*p)();
  
  p=f;
  
  p();
  
  assert(g==2);
}
