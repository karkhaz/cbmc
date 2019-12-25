/*
 * Author: Mark R. Tuttle <mrtuttle@amazon.com>
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 */

#include <assert.h>

/*****************************************************************/

uint32_t skip_colon(char *json, uint32_t length, uint32_t start);
uint32_t skip_comma(char *json, uint32_t length, uint32_t start);
uint32_t skip_whitespace(char *json, uint32_t length, uint32_t start);
uint32_t skip_string(char *json, uint32_t length, uint32_t start);
uint32_t skip_integer(char *json, uint32_t length, uint32_t start);
uint32_t skip_hash(char *json, uint32_t length, uint32_t start);
uint32_t skip_list(char *json, uint32_t length, uint32_t start);
uint32_t skip_value(char *json, uint32_t length, uint32_t start);
uint32_t hash_lookup(char *json, uint32_t jsonlength,
		     char *key, uint32_t keylength,
		     char **value, uint32_t *valuelength);

/*****************************************************************/

#ifndef AWS_PRECONDITION
#define AWS_PRECONDITION(predicate) assert(predicate)
#endif

#ifndef AWS_POSTCONDITION
#define AWS_POSTCONDITION(predicate) assert(predicate)
#endif

#ifndef AWS_MEM_IS_READABLE
#ifdef CBMC
#define AWS_MEM_IS_READABLE(base, len) __CPROVER_r_ok((base), (len))
#else
#define AWS_MEM_IS_READABLE(base, len) (base != NULL && len >= 0)
#endif
#endif

#ifndef AWS_MEM_IS_WRITABLE
#ifdef CBMC
#define AWS_MEM_IS_WRITABLE(base, len) __CPROVER_w_ok((base), (len))
#else
#define AWS_MEM_IS_WRITABLE(base, len) (base != NULL && len >= 0)
#endif
#endif

/*****************************************************************/

#define ERROR (0xFFFFFFFF)

#define IS_WHITESPACE(json, psn) (json[psn] == ' ' || \
				  json[psn] == '\t' || \
				  json[psn] == '\n' || \
				  json[psn] == '\f')
#define IS_DIGIT(json, psn) ('0' <= json[psn] && json[psn] <= '9')

#define IS_QUOTE(json, psn) (json[psn] == '"' && \
			     (psn == 0 || json[psn-1] != '\\'))
#define IS_COLON(json, psn) (json[psn] == ':')
#define IS_COMMA(json, psn) (json[psn] == ',')
#define IS_HASH_OPEN(json, psn) (json[psn] == '{')
#define IS_HASH_CLOSE(json, psn) (json[psn] == '}')
#define IS_LIST_OPEN(json, psn) (json[psn] == '[')
#define IS_LIST_CLOSE(json, psn) (json[psn] == ']')

/*****************************************************************/

#define SKIP_COLON_PRECOND(json, length, start) \
  AWS_MEM_IS_READABLE(json, length)
#define SKIP_COLON_POSTCOND(json, length, start, end) \
  (end == ERROR || \
   start < length && end == start+1 && end <= length && \
   IS_COLON(json, start))

#define SKIP_COMMA_PRECOND(json, length, start) \
  AWS_MEM_IS_READABLE(json, length)
#define SKIP_COMMA_POSTCOND(json, length, start, end) \
  (end == ERROR || \
   start < length && end == start+1 && end <= length && \
   IS_COMMA(json, start))

#define SKIP_WHITESPACE_PRECOND(json, length, start) \
  AWS_MEM_IS_READABLE(json, length)
#define SKIP_WHITESPACE_POSTCOND(json, length, start, end) \
  (end == ERROR || \
   (start < length && start <= end && end <= length && \
    (start == end || IS_WHITESPACE(json, end-1))))

#define SKIP_STRING_PRECOND(json, length, start) \
  AWS_MEM_IS_READABLE(json, length)
#define SKIP_STRING_POSTCOND(json, length, start, end) \
  (end == ERROR || \
   (start < length && start + 2 <= end && end <= length && \
    IS_QUOTE(json, start) && IS_QUOTE(json, end-1)))

#define SKIP_INTEGER_PRECOND(json, length, start) \
  AWS_MEM_IS_READABLE(json, length)
#define SKIP_INTEGER_POSTCOND(json, length, start, end) \
  (end == ERROR || \
   (start < length && start < end && end < length && \
    IS_DIGIT(json, start) && IS_DIGIT(json, end-1)))

#define SKIP_HASH_PRECOND(json, length, start) \
  AWS_MEM_IS_READABLE(json, length)
#define SKIP_HASH_POSTCOND(json, length, start, end) \
  (end == ERROR || \
   (start < length && start + 2 <= end && end <= length && \
    IS_HASH_OPEN(json, start) && IS_HASH_CLOSE(json, end-1)))

#define SKIP_LIST_PRECOND(json, length, start) \
  AWS_MEM_IS_READABLE(json, length)
#define SKIP_LIST_POSTCOND(json, length, start, end) \
  (end == ERROR || \
   (start < length && start + 2 <= end && end <= length && \
    IS_LIST_OPEN(json, start) && IS_LIST_CLOSE(json, end-1)))

#define SKIP_VALUE_PRECOND(json, length, start) \
  AWS_MEM_IS_READABLE(json, length)
#define SKIP_VALUE_POSTCOND(json, length, start, end) \
  (end == ERROR || (start < length && start < end && end <= length))

#define LOOKUP_PRECOND(json, jlength, key, klength, value, vlength) \
  (AWS_MEM_IS_READABLE(json, jlength) && \
   AWS_MEM_IS_READABLE(key, klength))
#define LOOKUP_POSTCOND(json, jlength, key, klength, value, vlength) (1)

/*****************************************************************/
