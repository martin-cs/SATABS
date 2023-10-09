int x, y;

int main(int argc, char **argv)
{
  int i;

  x = i;
  y = x;

  while(x!=0)
  {
    x--;
    y--;
  }
  
  assert(y == 0);
}
