#include <stdlib.h>

#include "proof.h"  // must come before jsonparser.h
#include "jsonparser.h"

int main(){

  char *json = malloc(nondet_sizet());
  uint32_t length;
  uint32_t start;

  __CPROVER_assume(length < LEN);
  AWS_PRECONDITION(SKIP_COLON_PRECOND(json, length, start));
  skip_colon(json, length, start);
}
