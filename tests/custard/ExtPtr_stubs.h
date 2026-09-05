#ifndef __EXTPTR_STUBS_H
#define __EXTPTR_STUBS_H
#include <stdint.h>
#include <stddef.h>
static uint8_t extptr_storage = 7;
/* Returns void *, as a C macro over untyped memory naturally does. */
#define extptr_base(off) ((void *)(&extptr_storage + (off)))
#endif
