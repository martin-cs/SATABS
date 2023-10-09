
int main(void)
{
  unsigned l_var;

  while (l_var!=0 && // otherwise 0<<1=0 forever.
         l_var<1073741824) {
    l_var = l_var << 1;
  }
}
