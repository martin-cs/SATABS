#ifdef SATABS
#define assert(e) __CPROVER_assert(e,"error")

#define acquire(m) \
{ \
  __CPROVER_atomic_begin(); \
	__CPROVER_assume(m==0); \
	m = 1; \
	__CPROVER_atomic_end(); \
} \

#define release(m) \
{ \
  __CPROVER_atomic_begin(); \
	__CPROVER_assume(m==1); \
	m = 0; \
	__CPROVER_atomic_end(); \
} \

#endif

int mThread=0;
int start_main=0;
int mStartLock=0;
int __COUNT__ =0;


int thr1() { //nsThread::Init (mozilla/xpcom/threads/nsThread.cpp 1.31)

  int PR_CreateThread__RES = 1;
  acquire(mStartLock);
  start_main=1;
#ifdef SATABS
  { __CPROVER_atomic_begin();
#else
  { __blockattribute__((atomic))
#endif
      if( __COUNT__ == 0 ) { // atomic check(0);
	mThread = PR_CreateThread__RES; 
	__COUNT__ = __COUNT__ + 1; 
      } else { assert(0); } 
#ifdef SATABS
  __CPROVER_atomic_end(); }
#else
  }
#endif
  release(mStartLock);
  if (mThread == 0) { return -1; }
  else { return 0; }

}

void thr2() { //nsThread::Main (mozilla/xpcom/threads/nsThread.cpp 1.31)

  int self = mThread;
  while (start_main==0);
  acquire(mStartLock);
  release(mStartLock);
#ifdef SATABS
  { __CPROVER_atomic_begin();
#else
  { __blockattribute__((atomic))
#endif
      if( __COUNT__ == 1 ) { // atomic check(1);
	int rv = self; // self->RegisterThreadSelf();
	__COUNT__ = __COUNT__ + 1;
      } else { assert(0); } 
#ifdef SATABS
  __CPROVER_atomic_end(); }
#else
  }
#endif
}


#ifdef SATABS 
int main()
{
  __CPROVER_ASYNC_1: thr1();
  thr2();
}
#endif
