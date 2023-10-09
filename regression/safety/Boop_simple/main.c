//#include <assert.h>

int usecount;
int locked;

int dummy_open ()
{
  usecount = usecount + 1;

  if (locked)
    return -1;
  locked = 1;
 
  return 0; /* success */
}

int dummy_release ()
{
  usecount = usecount - 1;
  locked = 0;
  return 0;
}

int unregister_chrdev ()
{
  if (usecount != 0)
    {
    // this should fail
    ERROR: assert (0);
    }
  else
    return 0;
}

int main ()
{
  int            rval;
  int count;

  usecount = 0;
  locked = 0;
  
  dummy_open ();

  do
    {
      rval = dummy_open ();
      if (rval == 0)
	{
	  count = 1;
	  dummy_release ();
	}
      else
	count = 0;
    }
  while	(count != 0);

  dummy_release ();

  unregister_chrdev ();

  return 0;
}
