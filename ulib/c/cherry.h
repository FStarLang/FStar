/* Runtime support for F* code extracted with --custard_backend Cherry.
   See cherry.md.  Generated units include this header; put the directory
   $(fstar.exe --locate_lib)/ulib/c on the C include path.

   A cell starts with a [cherry_obj] header.  Its reference count is positive
   while the cell is reachable from one thread only, negative (its magnitude
   counting the references) once it has been marked shared, and zero for an
   immortal cell.  A pointer with its low bit set is a constructor without
   fields, and the rest of it is the tag. */
#ifndef CHERRY_H
#define CHERRY_H

#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>

typedef struct cherry_obj { int32_t rc; uint32_t tag; } cherry_obj;

#define CHERRY_SCALAR(t) ((cherry_obj *)(((uintptr_t)(t) << 1) | 1u))

static inline bool cherry_is_scalar(const cherry_obj *o) {
  return ((uintptr_t)o & 1u) != 0;
}

static inline uint32_t cherry_tag(const cherry_obj *o) {
  return cherry_is_scalar(o) ? (uint32_t)((uintptr_t)o >> 1) : o->tag;
}

static inline cherry_obj *cherry_alloc(size_t size, uint32_t tag) {
  cherry_obj *o = (cherry_obj *)malloc(size);
  if (o == NULL) abort();
  o->rc = 1;
  o->tag = tag;
  return o;
}

static inline void cherry_inc(cherry_obj *o) {
  if (cherry_is_scalar(o)) return;
  int32_t rc = o->rc;
  if (rc > 0) o->rc = rc + 1;
  else if (rc < 0) __atomic_fetch_sub(&o->rc, 1, __ATOMIC_RELAXED);
}

/* Drop a reference; true when it was the last one and the cell has to be
   freed. */
static inline bool cherry_dec_ref(cherry_obj *o) {
  if (cherry_is_scalar(o)) return false;
  int32_t rc = o->rc;
  if (rc == 1) return true;
  if (rc > 1) { o->rc = rc - 1; return false; }
  if (rc == 0) return false;
  return __atomic_add_fetch(&o->rc, 1, __ATOMIC_ACQ_REL) == 0;
}

/* Mark a cell shared; true when it was not already, so that its fields
   have to be marked too. */
static inline bool cherry_mark_ref(cherry_obj *o) {
  if (cherry_is_scalar(o) || o->rc <= 0) return false;
  o->rc = -o->rc;
  return true;
}

#endif
