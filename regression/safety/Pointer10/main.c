void PrintFormatNumber(void * ValuePtr, int Format, int ByteCount)
{
  int s, n;      

  for(n=0;n<16;n++)
    ValuePtr = (void *)((char *)ValuePtr+s);
}

int main()
{
  int x;
  PrintFormatNumber(&x, x, x);
}
