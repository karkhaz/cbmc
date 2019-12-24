/*
 * Pure-functional recursive-descent JSON parser
 *
 * Author: Mark R. Tuttle <mrtuttle@amazon.com>
 *
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 */

#include <stdlib.h>
#include <string.h>

#include "jsonparser.h"

#ifdef CBMC
#define dump(name, json, start, end)
#else
#include <stdio.h>
#define dump(name, json, start, end) \
  if (end == ERROR) printf("error\n"); else {	\
  printf("%s = '", name); \
  for (int i=start; i < end; i++) printf("%c", json[i]); \
  printf("'\n"); }
#endif

/****************************************************************/

uint32_t skip_colon(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_COLON_PRECOND(json, length, start));

  uint32_t end = start;
  end = (start < length && end < length && IS_COLON(json, end)) ? end+1 : ERROR;

  AWS_POSTCONDITION(SKIP_COLON_POSTCOND(json, length, start, end));
  return end;
}

uint32_t skip_comma(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_COMMA_PRECOND(json, length, start));

  uint32_t end = start;
  end = (start < length && end < length && IS_COMMA(json, end)) ? end+1 : ERROR;

  AWS_POSTCONDITION(SKIP_COMMA_POSTCOND(json, length, start, end));
  return end;
}


uint32_t skip_whitespace(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_WHITESPACE_PRECOND(json, length, start));

  uint32_t end = start;
  end = (start < length && end < length) ? end : ERROR;
  while (end < length && IS_WHITESPACE(json, end)) end++;
  end = (end < length) ? end : ERROR;

  AWS_POSTCONDITION(SKIP_WHITESPACE_POSTCOND(json, length, start, end));
  return end;
}

/****************************************************************/

uint32_t skip_string(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_STRING_PRECOND(json, length, start));

  uint32_t end = start;
  end = (start < length && end < length && IS_QUOTE(json, end)) ? end+1 : ERROR;

  while (end < length && !IS_QUOTE(json, end)) end++;

  end = (end < length && IS_QUOTE(json, end)) ? end+1 : ERROR;

  dump("string", json, start, end);
  AWS_POSTCONDITION(SKIP_STRING_POSTCOND(json, length, start, end));
  return end;
}

uint32_t skip_integer(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_INTEGER_PRECOND(json, length, start));

  uint32_t end = start;
  end = (start < length && end < length && IS_DIGIT(json, end)) ? end+1 : ERROR;
  while (end < length && IS_DIGIT(json, end)) end++;
  end = (end < length) ? end : ERROR;

  dump("integer", json, start, end);
  AWS_POSTCONDITION(SKIP_INTEGER_POSTCOND(json, length, start, end));
  return end;
}

/****************************************************************/

uint32_t skip_hash(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_HASH_PRECOND(json, length, start));

  uint32_t end = start;
  end = (start < length && end < length && IS_HASH_OPEN(json, end)) ? end+1 : ERROR;
  end = skip_whitespace(json, length, end);  // hash may be empty

  while (end < length && !IS_HASH_CLOSE(json, end)) {
    end = skip_whitespace(json, length, end);
    end = skip_string(json, length, end);
    end = skip_whitespace(json, length, end);
    end = skip_colon(json, length, end);
    end = skip_whitespace(json, length, end);
    end = skip_value(json, length, end);
    end = skip_whitespace(json, length, end);
    if (end < length && IS_COMMA(json, end)) end++; else break;
  }

  end = (end < length && IS_HASH_CLOSE(json, end)) ? end+1 : ERROR;

  dump("hash", json, start, end);
  AWS_POSTCONDITION(SKIP_HASH_POSTCOND(json, length, start, end));
  return end;
}

uint32_t skip_list(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_LIST_PRECOND(json, length, start));

  uint32_t end = start;
  end = (start < length && end < length && IS_LIST_OPEN(json, end)) ? end+1 : ERROR;
  end = skip_whitespace(json, length, end);  // list may be empty

  while (end < length && !IS_LIST_CLOSE(json, end)) {
    end = skip_whitespace(json, length, end);
    end = skip_value(json, length, end);
    end = skip_whitespace(json, length, end);
    if (end < length && IS_COMMA(json, end)) end++; else break;
  }

  end = (end < length && IS_LIST_CLOSE(json, end)) ? end+1 : ERROR;

  dump("list", json, start, end);
  AWS_POSTCONDITION(SKIP_LIST_POSTCOND(json, length, start, end));
  return end;
}

/****************************************************************/

uint32_t skip_value(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_VALUE_PRECOND(json, length, start));

  uint32_t end = start;
  if (end < length && IS_QUOTE(json, end))
    end = skip_string(json, length, end);
  if (end < length && IS_DIGIT(json, end))
    end = skip_integer(json, length, end);
  if (end < length && IS_HASH_OPEN(json, end))
    end = skip_hash(json, length, end);
  else if (end < length && IS_LIST_OPEN(json, end))
    end = skip_list(json, length, end);
  else
    end = ERROR;

  dump("value", json, start, end);
  AWS_POSTCONDITION(SKIP_VALUE_POSTCOND(json, length, start, end));
  return end;
}

/****************************************************************/

uint32_t hash_lookup(char *json, uint32_t jsonlength,
		     char *key, uint32_t keylength,
		     char **value, uint32_t *valuelength) {
  AWS_PRECONDITION(LOOKUP_PRECOND(json, jsonlength,
				  key, keylength,
				  value, valuelength));

  uint32_t end = 0;
  uint32_t keystart = 0, keyend = 0, valuestart = 0, valueend = 0;

  *value = 0;
  *valuelength = 0;

  end = skip_whitespace(json, jsonlength, end);
  end = (end < jsonlength && IS_HASH_OPEN(json, end)) ? end+1 : ERROR;
  end = skip_whitespace(json, jsonlength, end);  // hash may be empty

  while (end < jsonlength && !IS_HASH_CLOSE(json, end)) {
    keystart = skip_whitespace(json, jsonlength, end);
    keyend = skip_string(json, jsonlength, keystart);
    end = skip_whitespace(json, jsonlength, keyend);
    end = skip_colon(json, jsonlength, end);
    valuestart = skip_whitespace(json, jsonlength, end);
    valueend = skip_value(json, jsonlength, valuestart);
    end = skip_whitespace(json, jsonlength, valueend);
    if (end != ERROR &&
	keyend - keystart - 2 == keylength &&
	strncmp(&json[keystart+1], key, keylength) == 0) {
      *value = &json[valuestart];
      *valuelength = valueend - valuestart;
      break;
    }
    if (end < jsonlength && IS_COMMA(json, end)) end++; else break;
  }

  AWS_POSTCONDITION(LOOKUP_POSTCOND(json, jsonlength,
				    key, keylength,
				    value, valuelength));
  return *value != 0;
}

/****************************************************************/

