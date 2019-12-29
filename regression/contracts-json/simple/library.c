/*
 * Purely-functional functions
 *
 * Author: Kareem Khazem <karkhaz@karkhaz.com>
 *
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 */

#include <stdlib.h>

int get_at_idx(
    int const *const arr,
    const size_t len,
    const size_t idx)
__CPROVER_requires(__CPROVER_r_ok(arr, len) && idx < len)
__CPROVER_ensures(arr[idx] == __CPROVER_return_value)
{
  return arr[idx];
}

void safe_get_at_idx()
{
  int a[5] = {0};
  get_at_idx(a, 5, 3);
}
