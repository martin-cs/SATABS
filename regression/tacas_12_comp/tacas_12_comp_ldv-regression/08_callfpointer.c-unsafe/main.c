/* Generated by CIL v. 1.3.7 */
/* print_CIL_Input is true */

#line 5 "files/callfpointer.c"
void f(void (*g)(int  ) ) 
{ 

  {
  {
#line 6
  (*g)(1);
  }
#line 7
  return;
}
}
#line 9 "files/callfpointer.c"
void h(int i ) 
{ 

  {
#line 10
  if (i == 1) {
    ERROR: 
#line 11
    goto ERROR;
  } else {

  }
#line 15
  return;
}
}
#line 16 "files/callfpointer.c"
int main(void) 
{ 

  {
  {
#line 17
  f(& h);
  }
#line 19
  return (0);
}
}
