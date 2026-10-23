#ifndef CASTSUBSCRIPT_STUBS_H
#define CASTSUBSCRIPT_STUBS_H

#include <stddef.h>
#include <stdint.h>

static uint32_t cast_subscript_cell = 7;
static uint32_t cast_subscript_macro_cell = 13;
static uint32_t cast_subscript_storage[2] = {19, 19};

static inline void *cast_subscript_ref(size_t off)
{
  return &cast_subscript_cell + off;
}

static inline void *cast_subscript_array(size_t off)
{
  return cast_subscript_storage + off;
}

#define cast_subscript_macro_ref(off) \
  1 ? (void *)(&cast_subscript_macro_cell + (off)) : (void *)0

#endif
