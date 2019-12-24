/*
 * Author: Mark R. Tuttle <mrtuttle@amazon.com>
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 */

#include <stdlib.h>

#include "proof.h"  // must come before jsonparser.h
#include "jsonparser.h"

int main(){

  char *json = malloc(nondet_sizet());
  uint32_t length;
  uint32_t start;

  __CPROVER_assume(length < LEN);
  AWS_PRECONDITION(SKIP_COMMA_PRECOND(json, length, start));
  skip_comma(json, length, start);
}
