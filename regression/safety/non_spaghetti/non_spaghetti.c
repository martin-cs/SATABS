void foo()
{
  int i, j;

  for(i=0; i<100; i++)
    {
      for(j = i+1; j<101; j++)
	{
	  assert(j>i);
	}
    }

  assert(i==100);
}
