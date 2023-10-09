int main ()
{
  int i;
  int tmp;

  for (i = 0; i < 5; )
    {
      tmp = i;
      tmp++;
      i = tmp;
    }

  if (i < 6)
  assert (i != 5);
}
