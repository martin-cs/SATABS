int main()
{
  _Bool *p;
  _Bool buffer[8*8];
  int i;

  p=buffer;

  for(i=0; i<8; i++)
  {
    assert(p==buffer+i);
    p++;
  }
}
