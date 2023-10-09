

int main() {
  int i, j;

  i = 0;
  goto outer;

 inner_end:
  i = i+1;
  goto outer;

 outer_end:
  goto end;

 outer:
  if(i >= 100) goto outer_end;
  j = i+1;
  goto inner;
  



 inner:
  if(j >= 101) goto inner_end;

  assert(j > i+1);
  j++;
  goto inner;

 end:
  assert(i==100);
  return i;
}
