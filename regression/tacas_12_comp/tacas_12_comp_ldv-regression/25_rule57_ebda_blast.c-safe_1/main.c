/* Generated by CIL v. 1.3.7 */
/* print_CIL_Input is true */

#line 10 "files/rule57_ebda_blast.c"
struct hotplug_slot;
#line 10
struct hotplug_slot;
#line 12 "files/rule57_ebda_blast.c"
struct bus_info {

};
#line 15 "files/rule57_ebda_blast.c"
struct slot {
   int a ;
   int b ;
   struct hotplug_slot *hotplug_slot ;
   struct bus_info *bus_on ;
};
#line 22 "files/rule57_ebda_blast.c"
struct hotplug_slot {
   struct slot *private ;
   int b ;
};
#line 2 "./assert.h"
void __blast_assert(void) 
{ 

  {
  ERROR: 
#line 4
  goto ERROR;
}
}
#line 32 "files/rule57_ebda_blast.c"
struct slot *tmp_slot  ;
#line 33 "files/rule57_ebda_blast.c"
int used_tmp_slot  =    0;
#line 34 "files/rule57_ebda_blast.c"
int freed_tmp_slot  =    1;
#line 36
extern void *kzalloc(int  , int  ) ;
#line 38 "files/rule57_ebda_blast.c"
void kfree(void *p ) 
{ void *__cil_tmp2 ;
  unsigned int __cil_tmp3 ;
  unsigned int __cil_tmp4 ;
  unsigned int __cil_tmp5 ;
  unsigned int __cil_tmp6 ;

  {
  {
#line 39
  __cil_tmp2 = (void *)0;
#line 39
  __cil_tmp3 = (unsigned int )__cil_tmp2;
#line 39
  __cil_tmp4 = (unsigned int )p;
#line 39
  if (__cil_tmp4 != __cil_tmp3) {
    {
#line 39
    __cil_tmp5 = (unsigned int )tmp_slot;
#line 39
    __cil_tmp6 = (unsigned int )p;
#line 39
    if (__cil_tmp6 == __cil_tmp5) {
#line 40
      freed_tmp_slot = 1;
    } else {

    }
    }
  } else {

  }
  }
#line 41
  return;
}
}
#line 44
extern void *__VERIFIER_nondet_pointer(void) ;
#line 45 "files/rule57_ebda_blast.c"
static struct bus_info *ibmphp_find_same_bus_num(void) 
{ void *tmp ;

  {
  {
#line 47
  tmp = __VERIFIER_nondet_pointer();
  }
#line 47
  return ((struct bus_info *)tmp);
}
}
#line 46
extern int __VERIFIER_nondet_int(void) ;
#line 47 "files/rule57_ebda_blast.c"
static int fillslotinfo(struct hotplug_slot *ptr ) 
{ int tmp ;

  {
  {
#line 49
  tmp = __VERIFIER_nondet_int();
  }
#line 49
  return (tmp);
}
}
#line 47 "files/rule57_ebda_blast.c"
static int ibmphp_init_devno(struct slot **ptr ) 
{ int tmp ;

  {
  {
#line 49
  tmp = __VERIFIER_nondet_int();
  }
#line 49
  return (tmp);
}
}
#line 49 "files/rule57_ebda_blast.c"
int ebda_rsrc_controller(void) 
{ struct hotplug_slot *hp_slot_ptr ;
  struct bus_info *bus_info_ptr1 ;
  int rc ;
  void *tmp ;
  void *tmp___0 ;
  int __cil_tmp6 ;
  int __cil_tmp7 ;
  void *__cil_tmp8 ;
  struct slot **__cil_tmp9 ;
  struct slot *__cil_tmp10 ;
  void *__cil_tmp11 ;

  {
  {
#line 54
  __cil_tmp6 = (int )8U;
#line 54
  tmp = kzalloc(__cil_tmp6, 1);
#line 54
  hp_slot_ptr = (struct hotplug_slot *)tmp;
  }
#line 55
  if (! hp_slot_ptr) {
#line 56
    rc = -2;
#line 57
    goto error_no_slot;
  } else {

  }
  {
#line 59
  hp_slot_ptr->b = 5;
#line 61
  __cil_tmp7 = (int )16U;
#line 61
  tmp___0 = kzalloc(__cil_tmp7, 1);
#line 61
  tmp_slot = (struct slot *)tmp___0;
  }
#line 63
  if (! tmp_slot) {
#line 64
    rc = -2;
#line 65
    goto error_no_slot;
  } else {

  }
  {
#line 68
  used_tmp_slot = 0;
#line 69
  freed_tmp_slot = 0;
#line 71
  tmp_slot->a = 2;
#line 72
  tmp_slot->b = 3;
#line 74
  bus_info_ptr1 = ibmphp_find_same_bus_num();
  }
#line 75
  if (! bus_info_ptr1) {
    {
#line 76
    rc = -3;
#line 79
    __cil_tmp8 = (void *)tmp_slot;
#line 79
    kfree(__cil_tmp8);
#line 80
    freed_tmp_slot = 1;
    }
#line 82
    goto error;
  } else {

  }
  {
#line 84
  tmp_slot->bus_on = bus_info_ptr1;
#line 85
  bus_info_ptr1 = (struct bus_info *)0;
#line 87
  tmp_slot->hotplug_slot = hp_slot_ptr;
#line 89
  hp_slot_ptr->private = tmp_slot;
#line 90
  used_tmp_slot = 1;
#line 92
  rc = fillslotinfo(hp_slot_ptr);
  }
#line 93
  if (rc) {
#line 94
    goto error;
  } else {

  }
  {
#line 96
  __cil_tmp9 = & hp_slot_ptr->private;
#line 96
  rc = ibmphp_init_devno(__cil_tmp9);
  }
#line 97
  if (rc) {
#line 98
    goto error;
  } else {

  }
#line 100
  return (0);
  error: 
  {
#line 103
  __cil_tmp10 = hp_slot_ptr->private;
#line 103
  __cil_tmp11 = (void *)__cil_tmp10;
#line 103
  kfree(__cil_tmp11);
  }
  error_no_slot: 
#line 108
  return (rc);
}
}
#line 111 "files/rule57_ebda_blast.c"
void main(void) 
{ 

  {
  {
#line 112
  ebda_rsrc_controller();
  }
#line 113
  if (! used_tmp_slot) {
#line 114
    if (freed_tmp_slot) {

    } else {
      {
#line 114
      __blast_assert();
      }
    }
  } else {

  }
#line 115
  return;
}
}
