
#ifndef NTHREADS
#error NTHREADS should be passed as directive to the compiler, e.g. -DNTHREADS=2
#endif

#include <pthread.h>
#include <stdlib.h>
#include <assert.h>

#ifdef EXHIBIT_BUG
#include <unistd.h>
#endif

#ifdef BUG
int temp;
#endif

void* f(void* _ctx)
{
#ifndef BUG
  int temp;
#endif
  temp = 0;
#ifdef EXHIBIT_BUG
  usleep(100); // insert this to reveal the bug at runtime
#endif
  temp++;
  assert(temp == 1);
}

pthread_t threads[NTHREADS];

int main() {

  int i;

  for(i = 0; i < NTHREADS; i++)
    {

      /*if(pthread_create(&threads[i], NULL, f, NULL))
	{
	  exit(1);
	}*/ __CPROVER_ASYNC_1: f(0);

    }

  for(i = 0; i < NTHREADS; i++)
    {
      pthread_join(threads[i], NULL);
    }
 
}
