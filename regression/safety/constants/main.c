int main()
{
  int w, x, y, z;
  
  if(w)
  {
    x = x;
  }
      
  x = 2;  
  y = x;  
  z = y;

  if(x == 2)
  {
    x = x;
  }
  
  x = z;
  
  assert(z == 3);
}
