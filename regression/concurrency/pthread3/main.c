#define NULL 0

typedef int pthread_t;

int pthread_create(
  pthread_t *,
  void *,
  void * (*start_routine)(void *),
  void *);

int g;

void *thread1(void *arg)
{
  int a;
  
  a=*((int *)arg);

  assert(a==10);
}

void *thread2(void *arg)
{
  int a;
  
  a=*((int *)arg);

  assert(a==20);

  g=1;
}

int main()
{
  pthread_t id1, id2;
  
  int arg1=10, arg2=20;

  pthread_create(&id1, NULL, thread1, &arg1);
  pthread_create(&id2, NULL, thread2, &arg2);
  
  // this should fail because of thread2
  assert(g==0);
}
