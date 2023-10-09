int main()
{
  int x, i;
  
  struct
  {
    int x, i;
  } s;

  x=1;
  s.x=1;

  // can't get past this without path slicing
  for(i=0; i<100000; i++);

  // same inside a struct
  for(s.i=0; s.i<100000; s.i++);

  assert(x==2 || s.x==2);
}
