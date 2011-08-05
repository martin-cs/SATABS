#include "driver.h"

int usecount;
int dummy_major;

int register_chrdev (unsigned int major, const char* name)
{
  usecount = 0;
  if (major == 0)
    return MAJOR_NUMBER;
  return major;
}

int unregister_chrdev (unsigned int major, const char* name)
{
  if (MOD_IN_USE)
    {
    ERROR: assert (0);
    }
  else
    return 0;
}

int main ()
{
  int            rval;
  int            size;
  struct file    my_file;
  char          *buffer;
  struct inode   inode;
  unsigned int   count;

  dummy_major = register_chrdev (0, "dummy");
  inode.i_rdev = dummy_major << MINORBITS;

  init_module ();
  
  dummy_open (&inode, &my_file);

  do
    {
      rval = dummy_open (&inode, &my_file);
      if (rval == 0)
	{
	  count = dummy_read (&my_file, buffer, BUF_SIZE); 
	  dummy_release (&inode, &my_file);
	}
      else
	count = 0;
    }
  while	(count != 0);

  dummy_release (&inode, &my_file);

  cleanup_module ();
  unregister_chrdev (dummy_major, "dummy");

  return 0;
}
