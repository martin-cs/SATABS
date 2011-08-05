#define NULL 0

typedef int pthread_t;

int pthread_create(pthread_t *, void *, void *, void *);

int g;

void *t1(void *arg)
{
  int a1, *aptr1;
  
  aptr1=(int *)arg;
  a1=*aptr1;

  // this should pass
  assert(a1==10);
}

void *t2(void *arg)
{
  int a2, *aptr2;
  
  aptr2=(int *)arg;
  a2=*aptr2;

  // this should pass
  assert(a2==20);
}

int main()
{
  pthread_t id1, id2;
  
  int arg1=10, arg2=20;

  pthread_create(&id1, NULL, t1, &arg1);
  pthread_create(&id2, NULL, t2, &arg2);

  assert(g==0);
}
