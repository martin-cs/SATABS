#include "driver.h"

extern int dummy_major;
int locked;

int init_module (void)
{
  locked = FALSE;
}

void cleanup_module (void) { }

int dummy_open (struct inode *inode, struct file *filp)
{
  assert (MAJOR (inode->i_rdev) == dummy_major);
  MOD_INC_USE_COUNT;

  if (locked)
    return -1;
  locked = TRUE;
 
  return 0; /* success */
}

unsigned int dummy_read (struct file *filp, char *buf, int max)
{
  int n;
  return n;
}

int dummy_release (struct inode *inode, struct file *filp)
{
  MOD_DEC_USE_COUNT;
  locked = FALSE;
  return 0;
}

