#include <pthread.h>
#include <stdio.h>

pthread_mutex_t mutex;
pthread_cond_t cond;

_Bool glob;

void *thread(void *p)
{
  pthread_mutex_lock(&mutex);

  pthread_cond_wait(&cond, &mutex);
  glob=1;

  // we now have the mutex again!
  pthread_mutex_unlock(&mutex);

  pthread_cond_destroy(&cond);  
}

int main()
{
  pthread_mutex_init(&mutex, 0);
  pthread_cond_init(&cond, 0);            

  pthread_t t;
  pthread_create(&t, 0, thread, 0);
  
  // the lock isn't held while waiting for "cond"!
  pthread_mutex_lock(&mutex);
  pthread_mutex_unlock(&mutex);
  
  assert(!glob);
  pthread_cond_signal(&cond);
}

