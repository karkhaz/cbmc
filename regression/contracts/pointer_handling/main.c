#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>

int global = 0;
int *global_ptr = malloc(sizeof(int));

int modify_object(int *const ptr)
__CPROVER_requires(
    __CPROVER_r_ok(ptr, sizeof(int *)) &&
    // TODO
    // Hmm, it seems to me that we should require that *ptr is readable as well
    // as writeable, since we're effectively doing *ptr = *ptr - 1;. Not sure
    // why this verifies even when we don't do __CPROVER_r_ok.
    __CPROVER_w_ok(*ptr, sizeof(int)) &&
    ptr != NULL &&
    *ptr > INT_MIN)
__CPROVER_ensures(__CPROVER_return_value == 0)
{
  --(*ptr);
  return 0;
}

int modify_pointer(int const **p1, int const *p2)
__CPROVER_requires(
    __CPROVER_r_ok(p1, sizeof(int **)) &&
    __CPROVER_r_ok(*p1, sizeof(int *)) &&
    __CPROVER_r_ok(**p1, sizeof(int)))
__CPROVER_ensures(__CPROVER_return_value == 0)
{
  *p1 = p2;
  return 0;
}

int modify_global()
__CPROVER_requires(global > INT_MIN)
__CPROVER_ensures(__CPROVER_return_value == 0)
{
  --global;
  return 0;
}

int modify_global_object()
__CPROVER_requires(
    __CPROVER_r_ok(global_ptr, sizeof(int *)) &&
    *global_ptr > INT_MIN)
__CPROVER_ensures(__CPROVER_return_value == 0)
{
  --(*global_ptr);
  return 0;
}

int main(){
  int stack_main = 0;
  int *malloc_main = malloc(sizeof(int));

  int stack_pass_main = 0;
  int *malloc_pass_main = malloc(sizeof(int));

  const int const_int = 0;

  modify_object(&stack_pass_main);
  modify_object(malloc_pass_main);

  modify_global();
  modify_global_object();

  modify_pointer(&malloc_pass_main, &const_int);
  assert(malloc_pass_main == const_int);
}
