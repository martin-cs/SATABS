int main ()
{
  int buffer[4];
  int i;
  int n = 5;
  int u = 0;


  for (i = 1; i < n; i ++)
    u +=buffer[i];

  assert (i == n);

}
