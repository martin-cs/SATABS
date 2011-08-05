int main()
{
  int *p;
  int **q;
  int x, y;
  int z;

  q=&p;  
  *q=z?&y:&z;
  
  z=*p;
}
