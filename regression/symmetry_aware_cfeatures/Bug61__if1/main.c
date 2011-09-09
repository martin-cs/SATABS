int main() {
	int i, j;

	i = 1;
	if(j > 0){
	  __CPROVER_assume(j > 0);
		j += i ;
	}else{
    __CPROVER_assume(!(j > 0));
		j = 0;
	}

	assert(i != j);
}
