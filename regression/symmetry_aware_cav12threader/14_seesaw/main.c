#ifdef SATABS
#define assert(e) __CPROVER_assert(e,"error")
#endif

int nondet() {int i; return i; }

//This example is adapted from StIng 
void thr1()
{
	int x;
	int y;

	if (! (x==0)) return;
	if (! (y==0)) return;

	while (nondet())
	{
		if (nondet())
		{
			if (! (x >= 9)) return;
			x = x + 2;
			y = y + 1;
		}
		else
		{
			if (nondet())
			{
				if (!(x >= 7)) return;
				if (!(x <= 9)) return;
				x = x + 1;
				y = y + 3;
			}
			else
			{
				if (nondet())
				{
					if (! (x - 5 >=0)) return;
					if (! (x - 7 <=0)) return;
					x = x + 2;
					y = y + 1;
				}
				else
				{
					if (!(x - 4 <=0)) return;
					x = x + 1;
					y = y + 2;
				}
			}
		}
	}
	assert (-x + 2*y  >= 0);
	assert (3*x - y  >= 0);
}

#ifdef SATABS 
int main()
{
  while(1)
  {
    __CPROVER_ASYNC_1: thr1();
  }
}
#endif
