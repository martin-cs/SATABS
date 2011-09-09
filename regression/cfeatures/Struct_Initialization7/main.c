struct X
{
  union Y
  {
    int a, b, c;
  } y;
  
  int z;
};

int main()
{
  struct X x={ 1, 2 };
  
  __CPROVER_assert(x.y.a==1, "true");
  __CPROVER_assert(x.z==2, "true");
}
