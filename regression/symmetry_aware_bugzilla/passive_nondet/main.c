unsigned input, s;

unsigned ctr = 0;
unsigned first = 1;

int f()
{

  unsigned l;

  __CPROVER_predicate(first);
  __CPROVER_predicate(l == input);
  __CPROVER_predicate(s == l);

  __CPROVER_predicate(ctr == 0);
  __CPROVER_predicate(ctr == 1);
  __CPROVER_predicate(ctr == 2);
  __CPROVER_predicate(ctr == 3);
  __CPROVER_predicate(ctr >= 4);
  
  l = input;

  ++ctr;
  __CPROVER_assume(ctr == 2);
  
  __CPROVER_atomic_begin();
  if(first)
  {
    s = l, first = 0;
  }
  else
  {
    assert(s == l);
  }
  __CPROVER_atomic_end();
 
}

int main()
{
  input = rand();
  while(1)
  {
    __CPROVER_ASYNC_01: f();
  }
}


