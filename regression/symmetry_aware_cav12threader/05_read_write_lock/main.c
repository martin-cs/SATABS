#ifdef SATABS
#define assert(e) __CPROVER_assert(e,"error")
#define assume(e) __CPROVER_assume(e)
#endif

int w, r, x, y;

void thr1() { //writer
#ifndef SATABS
  glb_init(w==0);
  glb_init(r==0);
#endif
#ifdef SATABS
  { __CPROVER_atomic_begin();
#else
  { __blockattribute__((atomic))
#endif
    assume(w==0);
    assume(r==0);
    w = 1;
#ifdef SATABS
  __CPROVER_atomic_end(); }
#else
  }
#endif
  x = 3;
  w = 0;
}

void thr2() { //reader
#ifdef SATABS
  { __CPROVER_atomic_begin();
#else
  { __blockattribute__((atomic))
#endif
    assume(w==0);
    r = r+1;
#ifdef SATABS
  __CPROVER_atomic_end(); }
#else
  }
#endif
  y = x;
  assert(y == x);
  r = r-1;
}

#ifdef SATABS 
int main()
{
  __CPROVER_assume(w==0);
  __CPROVER_assume(r==0);

  __CPROVER_ASYNC_1: thr1();
  thr2();
}
#endif
