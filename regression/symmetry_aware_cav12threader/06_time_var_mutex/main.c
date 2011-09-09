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

int block;
int busy; // boolean flag indicating whether the block has be an allocated to an inode
int inode;
int m_inode=0; // protects the inode
int m_busy=0; // protects the busy flag

thr1(){
#ifndef SATABS
  glb_init(inode == busy);
#endif
  acquire(m_inode);
  if(inode == 0){
    acquire(m_busy);
    busy = 1;
    release(m_busy);
    inode = 1;
  }
  block = 1;
  assert(block == 1);
  release(m_inode);
}

thr2(){
  acquire(m_busy);
  if(busy == 0){
    block = 0;
    assert(block == 0);
  }
  release(m_busy);
}

#ifdef SATABS 
int main()
{
  __CPROVER_assume(inode == busy);

  __CPROVER_ASYNC_1: thr1();
  thr2();
}
#endif
