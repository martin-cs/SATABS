#define SIZE(x) (sizeof(x) / sizeof(x[0]))
unsigned int nondet_uint();
typedef struct s { int n; } mailbox_t;

mailbox_t m1, m2, m3;
int main(void)
{
    mailbox_t *arr[] = {&m1, &m2, &m3};
    unsigned int ndet = nondet_uint();
    __CPROVER_assume(ndet < SIZE(arr));

    __CPROVER_assert(arr[ndet] == &m1 ||
             arr[ndet] == &m2 ||
             arr[ndet] == &m3, "E");
    return 0;
}

