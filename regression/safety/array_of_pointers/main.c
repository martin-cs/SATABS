#define SIZE(x) (sizeof(x) / sizeof(x[0]))
unsigned int nondet_uint();
typedef struct s { int n; } mailbox_t;

mailbox_t m1, m2, m3;
int main(void)
{
    mailbox_t *arr[] = {&m1, &m2, &m3};
    unsigned int ndet = nondet_uint();
    __CPROVER_assume(ndet < SIZE(arr));

    /*    __CPROVER_predicate(arr[0] == &m1);
    __CPROVER_predicate(arr[1] == &m2);
    __CPROVER_predicate(arr[2] == &m3);*/
    __CPROVER_predicate(ndet == 0);
    __CPROVER_predicate(ndet == 1);
    __CPROVER_predicate(ndet == 2);

    __CPROVER_assert(arr[ndet] == &m1 ||
             arr[ndet] == &m2 ||
             arr[ndet] == &m3, "E");
    return 0;
}
