#define AWS_PRECONDITION(predicate) __CPROVER_assume(predicate)
#define AWS_POSTCONDITION(predicate) __CPROVER_assert(predicate, "Postcondition")

