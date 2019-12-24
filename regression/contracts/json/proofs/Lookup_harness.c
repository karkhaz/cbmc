/*
 * Author: Mark R. Tuttle <mrtuttle@amazon.com>
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 */

#include <stdlib.h>

#include "proof.h"  // must come before jsonparser.h
#include "jsonparser.h"

int main(){

  char *json = malloc(nondet_sizet());
  uint32_t jsonlength;
  char *key = malloc(nondet_sizet());
  uint32_t keylength;
  char *value;
  uint32_t valuelength;

  __CPROVER_assume(jsonlength < LEN);
  __CPROVER_assume(keylength < KEYLEN);
  AWS_PRECONDITION(LOOKUP_PRECOND(json, jsonlength,
				  key, keylength,
				  &value, &valuelength));
  hash_lookup(json, jsonlength,
	      key, keylength,
	      &value, &valuelength);
}
