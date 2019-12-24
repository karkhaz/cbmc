/*
 * Author: Mark R. Tuttle <mrtuttle@amazon.com>
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 */

#define AWS_PRECONDITION(predicate) __CPROVER_assert(predicate, "Precondition")
#define AWS_POSTCONDITION(predicate) __CPROVER_assume(predicate)


