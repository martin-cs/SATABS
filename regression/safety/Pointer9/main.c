void *malloc(unsigned s);

/* list.h */
typedef struct node {
int d;
struct node *n;
} *L;

/* main.c */
int main() {
  L x, y, z, w;
  x = malloc(sizeof(struct node));
  x->n = malloc(sizeof(struct node));
  // should fail
  z=x->n->n->n->n;
}
