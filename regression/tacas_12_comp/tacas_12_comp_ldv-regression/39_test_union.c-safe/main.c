/* Generated by CIL v. 1.3.7 */
/* print_CIL_Input is true */

#line 10 "files/test_union.c"
union A {
   int list ;
   int l2 ;
   char *str ;
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
#line 16 "files/test_union.c"
int main(void) 
{ union A x ;

  {
#line 18
  x.list = 0;
#line 22
  if (x.list == 0) {

  } else {
    {
#line 22
    __blast_assert();
    }
  }
#line 24
  return (0);
}
}
