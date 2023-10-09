int s1;
int s2;
int main(){
	int v; 
	__CPROVER_predicate(v == s1);
	s1++;
	s2++;
	assert(s2 == 1);
	assert(0);
}
