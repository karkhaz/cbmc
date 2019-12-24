#include <stdlib.h>
#include <string.h>

#include "stub.h"  // must come before jsonparer.h
#include "jsonparser.h"

/****************************************************************/

#ifdef SKIP_COLON_STUB
uint32_t skip_colon(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_COLON_PRECOND(json, length, start));
  uint32_t end;
  AWS_POSTCONDITION(SKIP_COLON_POSTCOND(json, length, start, end));
  return end;
}
#endif

#ifdef SKIP_COMMA_STUB
uint32_t skip_comma(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_COMMA_PRECOND(json, length, start));
  uint32_t end;
  AWS_POSTCONDITION(SKIP_COMMA_POSTCOND(json, length, start, end));
  return end;
}
#endif

#ifdef SKIP_WHITESPACE_STUB
uint32_t skip_whitespace(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_WHITESPACE_PRECOND(json, length, start));
  uint32_t end;
  AWS_POSTCONDITION(SKIP_WHITESPACE_POSTCOND(json, length, start, end));
  return end;
}
#endif

#ifdef SKIP_STRING_STUB
uint32_t skip_string(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_STRING_PRECOND(json, length, start));
  uint32_t end;
  AWS_POSTCONDITION(SKIP_STRING_POSTCOND(json, length, start, end));
  return end;
}
#endif

#ifdef SKIP_INTEGER_STUB
uint32_t skip_integer(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_INTEGER_PRECOND(json, length, start));
  uint32_t end;
  AWS_POSTCONDITION(SKIP_INTEGER_POSTCOND(json, length, start, end));
  return end;
}
#endif

#ifdef SKIP_HASH_STUB
uint32_t skip_hash(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_HASH_PRECOND(json, length, start));
  uint32_t end;
  AWS_POSTCONDITION(SKIP_HASH_POSTCOND(json, length, start, end));
  return end;
}
#endif

#ifdef SKIP_LIST_STUB
uint32_t skip_list(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_LIST_PRECOND(json, length, start));
  uint32_t end;
  AWS_POSTCONDITION(SKIP_LIST_POSTCOND(json, length, start, end));
  return end;
}
#endif

#ifdef SKIP_VALUE_STUB
uint32_t skip_value(char *json, uint32_t length, uint32_t start) {
  AWS_PRECONDITION(SKIP_VALUE_PRECOND(json, length, start));
  uint32_t end;
  AWS_POSTCONDITION(SKIP_VALUE_POSTCOND(json, length, start, end));
  return end;
}
#endif
