int main ()
{
  int x, j, i;

  i = 2;
  j = 1;
  x = 3;

  while (1) {
    if (i < x)
      if (x < j) // diese Zeile verschwindet im GOTO-Programm
	break;
  }

  assert (0);
}
