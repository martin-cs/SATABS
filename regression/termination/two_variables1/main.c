
int main(void)
{
 unsigned x, y;

  while (x<100 && y<200) {
     if (nondet()) {
         x++;
     } else {
         y++;
     }
  }

}
