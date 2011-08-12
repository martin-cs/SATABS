#define MB_ID(n) (1ULL << n)
enum {
	mb1 = MB_ID(1),
	mb2 = MB_ID(2),
	mb3 = MB_ID(3),
	mb4 = MB_ID(42),
};


unsigned long long nondet_ull();
typedef struct s { int n; } mailbox_t;
unsigned int result;

#define AWAIT(...) ({ mailbox_t *p; result = nondet_ull(); p = await(__VA_ARGS__); p; })

mailbox_t *await(unsigned long long mmb)
{
	__CPROVER_assume(result < 64 && ((1ULL << result) & mmb));
	mailbox_t *_ret = (1ULL << result);
	return _ret;
}

int main(void)
{
	mailbox_t *m;
	
	m = AWAIT(mb1 | mb2 | mb4);
	
	if (m == (mailbox_t *)mb3)
		__CPROVER_assert(0, "E");
	return 0;
}
