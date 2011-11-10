int f(int a){ 
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
