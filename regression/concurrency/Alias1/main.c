#include <assert.h>
#include <stdlib.h>
#include <unistd.h>
#include <signal.h>
#include <pthread.h>

char *state="I00";

void my_thread()
{
  // set state to NULL
  state=NULL;
}

int main (int argc, char **argv)
{
  pthread_t t1;
  pthread_create(&t1, NULL, my_thread, NULL);

  sleep(1);

  // Possible null pointer and segmentation fault
  if(state[0]=='A')
    exit(1);

  return 0;
}
