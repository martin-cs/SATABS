/* Generated by CIL v. 1.3.7 */
/* print_CIL_Input is true */

#line 5 "files/test_address.c"
struct path_info {
   int list ;
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
#line 9 "files/test_address.c"
void list_add(int *new ) 
{ void *__cil_tmp2 ;
  unsigned int __cil_tmp3 ;
  unsigned int __cil_tmp4 ;

  {
  {
#line 10
  __cil_tmp2 = (void *)0;
#line 10
  __cil_tmp3 = (unsigned int )__cil_tmp2;
#line 10
  __cil_tmp4 = (unsigned int )new;
#line 10
  if (__cil_tmp4 != __cil_tmp3) {

  } else {
    {
#line 10
    __blast_assert();
    }
  }
  }
#line 11
  return;
}
}
#line 13 "files/test_address.c"
static void rr_fail_path(struct path_info *pi ) 
{ int *__cil_tmp2 ;

  {
  {
#line 15
  __cil_tmp2 = & pi->list;
#line 15
  list_add(__cil_tmp2);
  }
#line 16
  return;
}
}
#line 19 "files/test_address.c"
int main(void) 
{ struct path_info pi ;

  {
  {
#line 21
  rr_fail_path(& pi);
  }
#line 22
  return (0);
}
}
