int rand();

int calculateNext(int s2){
	int ret3;
	__CPROVER_predicate(ret3 == s2); //-> with this predicate: V.S., without: V.F. (bug caused by Boom, see https://bugs.comlab.ox.ac.uk/cprover/show_bug.cgi?id=66)

	do{
		ret3 = rand();
	}while(ret3 == s2 || ret3 == 0);
	__CPROVER_assume(!(ret3 == s2 || ret3 == 0)); 

  __CPROVER_assert(0, "this should fail");
}

int main(){
	calculateNext(1);
}
