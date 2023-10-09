int main (int argc, char** argv)
{
  int x, y, i, j;
  x = 0;
  y = 0;

  while (x<100)
    {
      x++;
      y++;
    }

  i = x;
  j = y;

  while (i<200)
    {
      i++;
      j++;
    }

  assert (j>=200);
}
