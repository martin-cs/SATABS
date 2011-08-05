int main ()
{
  int i;
  int j;
  int k;
  
  for (i = 0, j= 0; i < 5; )
    {
      i++;
      j = j + i + 1;
      k = j + 9;
    }
  
  if (j<21)
    assert (j != 20);
}

