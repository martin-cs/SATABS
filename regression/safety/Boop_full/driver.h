#ifndef __DRIVER_H__
#define __DRIVER_H__

#define MODULE
#include "modules.h"

#define TRUE   1
#define FALSE  0

#define BUF_SIZE 255

extern void assert (_Bool);
extern int init_module (void);
extern void cleanup_module (void);
extern int dummy_open (struct inode*, struct file*);
extern unsigned int dummy_read (struct file*, char*, int);
extern int dummy_release (struct inode*, struct file*);

#endif
