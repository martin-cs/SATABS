#include <pthread.h>

int count;

void __CPROVER_atomic_begin();
void __CPROVER_atomic_end();

void *my_thread(void *arg)
{
  __CPROVER_atomic_begin();
  count++;
  count--;
  __CPROVER_atomic_end();
}

int main(void)
{
  pthread_t id;

  pthread_create(&id, NULL, my_thread, NULL);

  __CPROVER_atomic_begin();
  __CPROVER_assert(count==0, "property");
  __CPROVER_atomic_end();

  return 0;
}
