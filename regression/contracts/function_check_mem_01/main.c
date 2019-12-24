#include <limits.h>
#include <stdlib.h>

typedef struct bar
{
  int x;
  int y;
  int z;
} bar;

void foo(bar *x)
  __CPROVER_requires(
      __CPROVER_r_ok(x, sizeof(bar)) &&
      __CPROVER_w_ok(x, sizeof(bar)) &&
      x->x < INT_MAX - 1)
  __CPROVER_ensures(1)
  // TODO
  // It would be nice to be able to refer to the values of x (and x->x) both at
  // function entry and exit. We should be able to write something like
  //
  //    __CPROVER_ensures(__CPROVER_initial(x->x) + 1 == __CPROVER_final(x->x))
{
  x->x += 1;
  return;
}

int main()
{
  bar *y = malloc(sizeof(bar));
  y->x = 0;
  foo(y);
}
