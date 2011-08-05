#include <stdarg.h>

void f(char *fmt, ...)
{
  va_list list;

  va_start(list, fmt);

  void *arg;
  unsigned i=0;

  while((arg=va_arg(list, void *))!=0)
  {
    i++;
  }

  va_end(list);
}

int main(void)
{
  void *p;

  f("pp", p, p);

  return 0;
}
