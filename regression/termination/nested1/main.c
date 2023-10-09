
int main(void)
{
  signed char x, y;

  while (x>0)
  {
    x++;
    y=1;

    while (y<x) { y++; }

    x=x-2;
  }
  
  return 0;
}
