
int g_dummy;

int f(void *p)
{
  int b=0;
  g_dummy++; // global; is a variant of the loop down there
}

unsigned long hdevcollection_count = 20;

int h_i;
void *gvar;

int main(void)
{
 if (hdevcollection_count != 0)
 {
  for (h_i=hdevcollection_count-1; h_i>0; h_i--)
  {
    int status=f(gvar);
    __CPROVER_assume(status>=0);
  }
}
}
