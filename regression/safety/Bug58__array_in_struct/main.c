struct T{ int _array[1]; };
struct T t[1];

int main(){
  int i = 0;
  t[i]._array[0] = 0;  
  __CPROVER_assert(t[i]._array[0] == 0, "true");
}
