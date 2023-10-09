// --max-new-iteration 1

/*
... `state == enum(1)'
 `tmp_condition$1'
 `return_value_nondet_uint$2 == 0'
 `mb == &c'
 `s->n == 0'
 `mb == &f'
 `_ret == &f'
 `m1 == &f'
 `m2 == &f'
 `m3 == &f'
 `tmp_condition$3'
 `&p1 == &s->n'
 `&c_g == &s->n'
 `&c_f == &s->n'
 `&c_e == &s->n'
 `&c_d == &s->n'
 `&c_c == &s->n'
 `&c_b == &s->n'
 `&c_a == &s->n'
 `&g == s'
 `&f == s'
 `&e == s'
 `&d == s'
 `&c == s'
 `&b == s'
 `&a == s'
 `&__CPROVER_rounding_mode == &s->n'
 `&__CPROVER_rounding_mode == &{ .n=0 }.n'
*/

#define NULL ((void*)0)
#define assert(x) __CPROVER_assert(x, "DE")

unsigned int nondet_uint(void);
typedef struct mailbox { int n; } mailbox_t;
enum { S1, S2, S3 } state;

mailbox_t a, b, c, d, e, f, g;
int c_a, c_b, c_c, c_d, c_e, c_f, c_g;

mailbox_t *AWAIT3(mailbox_t * m1, mailbox_t * m2, mailbox_t *m3)
{
	mailbox_t *_ret = (nondet_uint()? (nondet_uint()? m1 : m2) : m3);
	/* mailbox_t *_ret = (nondet_uint()? (nondet_uint()? m3 : m2) : m1); */
        if (state == S2) {
                assert((c_a == 1) && (c_b == 1));
                if ((_ret == &a) || (_ret == &b)) {
                        state = S3;
                        return _ret;
                }
        };
        return _ret;
}

void EMIT2(mailbox_t * mb, void *e, int p1)
{
	
        if ((mb == &(c))) {
                assert(state == S1);
                if (p1 == 0)
                        state = S2;
                else
                        state = S3;
        }
}

int main(void)
{
	mailbox_t *mb = 0;
	int rc;

	EMIT2(&d, NULL, 0);
	while (1) {
		mb = AWAIT3(&e, &f, &g);
		if (mb == &f) {
			mailbox_t *s /* = nondet_pointer() */;
			rc = s->n;
			break;
		}
	}
	EMIT2(&c, NULL, rc);
	c_b = 1;
	mb = AWAIT3(&b, &g, &d);
	return 0;
}
