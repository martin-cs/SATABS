int main(void)
{
  unsigned l_var, len;

  __CPROVER_assume(l_var>0);

  while (l_var < 1073741824 && 0<len) {

    if (len%2) { // was nondet()
        l_var = l_var << 1;
    } else {
        len--;
    }
  }
}
