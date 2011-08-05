int nondet_int();

int main()
{
  int *p;
  int i, j, x;

  i = 0;
  j = 1;

  if(nondet_int())
    p = &i;
  else
    p = &j;

  assert(*p==1);
}

