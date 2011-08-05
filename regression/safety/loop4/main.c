void my_sprintf(char *dummy)
{
  char *format = "a";

  int i; int n = 0;
  for (i = 0;; i++, n++)
  {
    // should be ok
    if (format[i] == 0)
      break;
  }

  for (i = 0;; i++, n++)
  {
    // will run out of bounds
    if (dummy[i] == 0)
      break;
  }
}

int main() 
{
  char dest_array[4];

  my_sprintf(dest_array);
  
  return 0;
}
