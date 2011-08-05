
int foo();

bar(){
  int a;
  a = 0 + foo();
  return a;
}

main(){
  int x,y;
  x = bar();
  y = bar();
  // this should fail,
  // as foo() returns something that is nondeterministically chosen
  assert(x == y);
}
