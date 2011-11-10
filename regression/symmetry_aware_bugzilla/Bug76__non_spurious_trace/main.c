//satabs  --modelchecker boom --full-inlining --max-cube-length 6 --min-threads 1 --max-threads 5 ./main3.c --strong-assume-length 6 --save-bps 
//--> "ref. failure" based on this trace 
//...
//TRACE t=0 PC21 b0_m_eq_0=1 b1_m_eq_6=0 b2_m_eq_7=0 b3_e_eq_6=0 b4_e_eq_7=1 b5_m_ge_e=0 b3_e_eq_6=1 b4_e_eq_7=0 b5_m_ge_e=0  --> m=0,e[0]=7,e[1]=6
//TRACE t=1 PC21 b0_m_eq_0=0             b2_m_eq_7=1                         b5_m_ge_e=1                         b5_m_ge_e=1  --> m=7,e[0]=7,e[1]=6
//TRACE t=0 PC22             b1_m_eq_6=1 b2_m_eq_7=0                         b5_m_ge_e=0                                      --> m=6,e[0]=7,e[1]=6 --> !(m>=e[0])
//which clearly is not spurious
volatile int m = 0;

void findmax(){
	int e;
	__CPROVER_predicate(e == 6);
	__CPROVER_predicate(e == 7);
	__CPROVER_assume(e == 6 || e == 7);
	m = e; 
	__CPROVER_assert(e <= m, "0");
}

int main() {
	__CPROVER_predicate(m == 0);
	__CPROVER_predicate(m == 6);
	__CPROVER_predicate(m == 7);
	while(1) { __CPROVER_ASYNC_1: findmax(); }
}
