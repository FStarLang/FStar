#ifndef __EXTBUF_STUBS_H
#define __EXTBUF_STUBS_H
#include <stdint.h>
#include <stddef.h>
static uint8_t extbuf_storage[4] = { 0, 1, 2, 3 };
/* Returns void *, as a C macro over untyped memory naturally does.  This is
   what makes the cast at the call site load-bearing: C converts void * to
   uint8_t * implicitly, C++ does not. */
#define extbuf_base(off) ((void *)(extbuf_storage + (off)))
/* Returns storage[0], which is 0, so main exits 0. */
static inline int32_t extbuf_use(uint8_t *a) { return (int32_t)a[0]; }
#endif
