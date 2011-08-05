// from Byron

_Bool nondet_Bool();

int main()
{
  unsigned l_var, old_l_var;
  int len, old_len;
  _Bool copied=0;

  __CPROVER_assume(l_var>0);

  while (l_var < 1073741824 && 0<len) {

     if (copied==1){
         assert(old_l_var<l_var && l_var<1073741924
                || old_len>len && len>0);
     } else if (nondet_Bool()) {
         copied=1;
         old_l_var = l_var;
         old_len = len;
     }

     if (nondet_Bool()) {
         l_var = l_var << 1;
     } else {
         len--;
     }
  }

}
