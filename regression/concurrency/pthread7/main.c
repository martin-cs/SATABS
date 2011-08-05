/* So to do threads it appears you need to include pthread.h which brings in the
 * appropriate prototypes, and to use the relevant functions to create the
 * threads.
 *
 * Hmm... but what about mutexes? */

#include <pthread.h>

int g;
pthread_mutex_t my_mutex;

void *thread1(void *arg)
{
        pthread_mutex_lock(&my_mutex); 
        g = 1;
        pthread_mutex_unlock(&my_mutex);
}

int main(void)
{
        pthread_t id1, id2;

        pthread_mutex_init(&my_mutex, NULL);

        pthread_create(&id1, NULL, thread1, NULL);

        // this may fail
        pthread_mutex_lock(&my_mutex);
        g = 0;
        assert(g == 0);
        pthread_mutex_unlock(&my_mutex);

        pthread_mutex_destroy(&my_mutex);

        return 0;
}
