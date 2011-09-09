int main(){
	int e;
	__CPROVER_predicate(e == 1);
	__CPROVER_predicate(e == 2);
	__CPROVER_assume(e == 1 && e == 2);
	__CPROVER_assert(0,"0");
}
