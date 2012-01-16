int main()
{
  // this should fail
  int pressure=10;

  if(pressure == 10)
    pressure=9;

  pressure++;

  assert(pressure == 11);

  return 0;
}

