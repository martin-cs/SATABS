/* Generated by CIL v. 1.3.7 */
/* print_CIL_Input is true */

#line 8 "files/nested_structure_ptr.c"
struct Innermost {
   int c ;
};
#line 8 "files/nested_structure_ptr.c"
struct Inner {
   int b ;
   struct Innermost *y ;
};
#line 8 "files/nested_structure_ptr.c"
struct Toplev {
   int a ;
   struct Inner *x ;
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
#line 18 "files/nested_structure_ptr.c"
int main(void) 
{ struct Innermost im ;
  struct Inner inner ;
  struct Toplev good ;
  struct Toplev *ptr ;
  struct Inner *__cil_tmp5 ;
  struct Innermost *__cil_tmp6 ;
  struct Inner *__cil_tmp7 ;
  struct Innermost *__cil_tmp8 ;
  int __cil_tmp9 ;

  {
#line 20
  im.c = 3;
#line 21
  inner.b = 2;
#line 21
  inner.y = & im;
#line 22
  good.a = 1;
#line 22
  good.x = & inner;
#line 23
  ptr = & good;
#line 24
  __cil_tmp5 = ptr->x;
#line 24
  __cil_tmp6 = __cil_tmp5->y;
#line 24
  __cil_tmp6->c = 4;
  {
#line 25
  __cil_tmp7 = ptr->x;
#line 25
  __cil_tmp8 = __cil_tmp7->y;
#line 25
  __cil_tmp9 = __cil_tmp8->c;
#line 25
  if (__cil_tmp9 == 4) {

  } else {
    {
#line 25
    __blast_assert();
    }
  }
  }
#line 26
  return (0);
}
}
