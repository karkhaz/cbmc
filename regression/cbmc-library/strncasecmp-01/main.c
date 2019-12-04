#include <assert.h>
#include <string.h>

int main() {
  char a[] = "abc";
  char b[] = "xyz";
  char A[] = "ABC";
  char B[] = "XYZ";
  assert(strncasecmp(a,b,0) == 0);
  assert(strncasecmp(A,B,0) == 0);
  assert(strncasecmp(A,b,0) == 0);
  assert(strncasecmp(A,b,2) == -1);
  assert(strncasecmp(B,a,2) == 1);
  return 0;
}
