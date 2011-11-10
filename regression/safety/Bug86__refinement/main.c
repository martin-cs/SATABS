unsigned int nondet_uint();

unsigned int result;

int f(unsigned int x)
{
#ifndef FIX
 	result = nondet_uint();
#endif
	__CPROVER_assume((1 << result) & x);
	return (1 << result);
}

int main(void)
{
#ifdef FIX
	result = nondet_uint();
#endif
	int m = f(1);
	assert(m != 2);
	return 0;
}
