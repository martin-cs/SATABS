int zz, yy;

void f()
{
  yy=1;
  assert(zz);
}

void g()
{
  yy=2;
  assert(!zz);
}

int main()
{
  void (*p)();
  int i;
  zz=i;

  p=i?f:g;
  
  p();
  
  if(i)
    assert(yy==1);
  else
    assert(yy==2);
}

