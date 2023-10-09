#include "basics.h"
#include <assert.h>

#undef MAX_ELEM
#define MAX_ELEM 1

enum lock_t {unlocked, locked} lock;

enum lock_t TestAndSet() {
	enum lock_t oldValue;
	atomic_begin();
	oldValue = lock;
	lock = locked;
	atomic_end();
	return oldValue;
}

extern void pause(int delay);

void aquire_lock(){
	int delay = 1;
	while(TestAndSet() == locked){
		pause(delay);
		if(delay*2 > delay) delay *= 2;
	}
}

void release_lock(){
	assert(lock != unlocked),
	lock = unlocked;
}

int s = 0;
int c = 0;
void test(){
	int l;
	aquire_lock();
	l = s;
	l++;
	s = l;
	release_lock();
	assert(s == l);
	c++;
}

int main(){
	__CPROVER_ASYNC_1: test();
	__CPROVER_ASYNC_2: test();
	//assert(c != 2 || s == 2);
}
