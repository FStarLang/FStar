/* Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
   Licensed under the Apache 2.0 License. */

#ifndef __KRML_STEEL_BASE_H
#define __KRML_STEEL_BASE_H

static inline bool within_bounds_ptr(void *left, void *p, void *right) {
  return (uintptr_t) left <= (uintptr_t) p && (uintptr_t) p < (uintptr_t) right;
}

#endif
