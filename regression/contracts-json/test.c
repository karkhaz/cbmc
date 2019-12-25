/*
 * Author: Mark R. Tuttle <mrtuttle@amazon.com>
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include "../jsonparser.h"
#include "../jsonparser.c"

int main() {
  char json[] = "{\"a\":{\"b\":\"c\"},\"hello\":\"kitty\"}";
  uint32_t length = strlen(json);
  uint32_t start, end;

  start = skip_whitespace(json, length, 0);
  end = skip_value(json, length, start);

  char json2[] = " \"abcde \" ";
  uint32_t length2 = strlen(json2);

  start = skip_whitespace(json2, length2, 0);
  end = skip_value(json2, length2, start);

  char *value;
  uint32_t valuelength;
  hash_lookup(json, length, "a", 1, &value, &valuelength);
  dump("hash lookup", value, 0, valuelength);
  hash_lookup(json, length, "hello", 5, &value, &valuelength);
  dump("hash lookup", value, 0, valuelength);

  char json3[] = "{ }";
  uint32_t length3 = strlen(json3);
  start = skip_whitespace(json3, length3, 0);
  end = skip_value(json3, length3, start);


}

