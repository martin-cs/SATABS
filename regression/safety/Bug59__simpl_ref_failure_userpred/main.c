int f(int a){ 
  __CPROVER_parameter_predicates();

	int r;
	__CPROVER_assume(r != a);
	return r; 
}

int main(){
	int i,j;
	i = rand();
	j = f(i); 
	assert(i != j);
}
