


int main()
{
	int x;
	int y;

	x = nondet();
	y = nondet();

	int z;

	if(x == y)
	{
		z = 0;
	} else {
		z = 1;
	}

	if(z == 0)
	{
		assert(x == y);
	} else {
		assert(x != y);
	}

	return 0;

}
