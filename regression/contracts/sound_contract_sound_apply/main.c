#include <assert.h>

int foo() 
  __CPROVER_ensures(__CPROVER_return_value == 1)
{
  return 1;
}

int main()
{
  int x = foo();
  assert(x == 1);
}
