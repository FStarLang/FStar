/* Runtime support for F* code extracted with --custard_backend Cherry.
   See cherry.md.  Generated units include this header; put the directory
   $(fstar.exe --locate_lib)/ulib/c on the C include path.

   A cell starts with a [cherry_obj] header.  Its reference count is positive
   while the cell is reachable from one thread only, negative (its magnitude
   counting the references) once it has been marked shared, and zero for an
   immortal cell.  A pointer with its low bit set is a constructor without
   fields, and the rest of it is the tag.

   Fast paths are inline here; the slow paths (big integers, string
   operations) are in cherry.c next to this file, which has to be compiled
   and linked with the program. */
#ifndef CHERRY_H
#define CHERRY_H

#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif

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

/* Cells allocated by the runtime itself, which have no counted fields. */
#define CHERRY_TAG_BIGINT 0xFFFFFFF0u
#define CHERRY_TAG_STRING 0xFFFFFFF1u

static inline void cherry_dec(cherry_obj *o) {
  if (cherry_dec_ref(o)) free(o);
}

static inline void cherry_mark(cherry_obj *o) {
  (void)cherry_mark_ref(o);
}

/* ------------------------------------------------------------------------
   Prims.int.  A tagged pointer: an odd value is a small integer shifted left
   by one, anything else is a big integer cell.  Every value is canonical --
   a number that fits in a small integer is never a cell -- so two small
   integers are equal exactly when their representations are. */

typedef cherry_obj *cherry_int;

#define CHERRY_INT_MAX (INTPTR_MAX >> 1)
#define CHERRY_INT_MIN (-CHERRY_INT_MAX - 1)
#define CHERRY_INT_SMALL(v) ((cherry_int)(((uintptr_t)(intptr_t)(v) << 1) | 1u))

static inline intptr_t cherry_int_val(cherry_int a) {
  return (intptr_t)(uintptr_t)a >> 1;
}

static inline bool cherry_int_fits(intptr_t v) {
  return v >= CHERRY_INT_MIN && v <= CHERRY_INT_MAX;
}

static inline bool cherry_int_both_small(cherry_int a, cherry_int b) {
  return ((uintptr_t)a & (uintptr_t)b & 1u) != 0;
}

cherry_int cherry_big_add(cherry_int a, cherry_int b);
cherry_int cherry_big_sub(cherry_int a, cherry_int b);
cherry_int cherry_big_mul(cherry_int a, cherry_int b);
cherry_int cherry_big_ediv(cherry_int a, cherry_int b);
cherry_int cherry_big_erem(cherry_int a, cherry_int b);
cherry_int cherry_big_neg(cherry_int a);
int cherry_big_cmp(cherry_int a, cherry_int b);
/* A literal too large for CHERRY_INT_SMALL on every platform. */
cherry_int cherry_int_of_decimal(const char *s);

static inline cherry_int cherry_int_add(cherry_int a, cherry_int b) {
  if (cherry_int_both_small(a, b)) {
    intptr_t r = cherry_int_val(a) + cherry_int_val(b);
    if (cherry_int_fits(r)) return CHERRY_INT_SMALL(r);
  }
  return cherry_big_add(a, b);
}

static inline cherry_int cherry_int_sub(cherry_int a, cherry_int b) {
  if (cherry_int_both_small(a, b)) {
    intptr_t r = cherry_int_val(a) - cherry_int_val(b);
    if (cherry_int_fits(r)) return CHERRY_INT_SMALL(r);
  }
  return cherry_big_sub(a, b);
}

static inline cherry_int cherry_int_mul(cherry_int a, cherry_int b) {
  if (cherry_int_both_small(a, b)) {
    intptr_t r;
    if (!__builtin_mul_overflow(cherry_int_val(a), cherry_int_val(b), &r) &&
        cherry_int_fits(r))
      return CHERRY_INT_SMALL(r);
  }
  return cherry_big_mul(a, b);
}

/* Euclidean division, as F*'s [/] and [%]: the remainder is never
   negative. */
static inline cherry_int cherry_int_div(cherry_int a, cherry_int b) {
  if (cherry_int_both_small(a, b)) {
    intptr_t x = cherry_int_val(a), y = cherry_int_val(b);
    if (y == 0) abort();
    intptr_t q = x / y, r = x % y;
    if (r < 0) q = y > 0 ? q - 1 : q + 1;
    if (cherry_int_fits(q)) return CHERRY_INT_SMALL(q);
  }
  return cherry_big_ediv(a, b);
}

static inline cherry_int cherry_int_mod(cherry_int a, cherry_int b) {
  if (cherry_int_both_small(a, b)) {
    intptr_t x = cherry_int_val(a), y = cherry_int_val(b);
    if (y == 0) abort();
    intptr_t r = x % y;
    if (r < 0) r = y > 0 ? r + y : r - y;
    return CHERRY_INT_SMALL(r);
  }
  return cherry_big_erem(a, b);
}

static inline cherry_int cherry_int_neg(cherry_int a) {
  if (cherry_is_scalar(a) && cherry_int_val(a) != CHERRY_INT_MIN)
    return CHERRY_INT_SMALL(-cherry_int_val(a));
  return cherry_big_neg(a);
}

static inline int cherry_int_cmp(cherry_int a, cherry_int b) {
  if (cherry_int_both_small(a, b)) {
    intptr_t x = cherry_int_val(a), y = cherry_int_val(b);
    return (x > y) - (x < y);
  }
  return cherry_big_cmp(a, b);
}

static inline bool cherry_int_eq(cherry_int a, cherry_int b) {
  if (a == b) return true;
  if (cherry_is_scalar(a) || cherry_is_scalar(b)) return false;
  return cherry_big_cmp(a, b) == 0;
}

static inline bool cherry_int_lt(cherry_int a, cherry_int b) { return cherry_int_cmp(a, b) < 0; }
static inline bool cherry_int_le(cherry_int a, cherry_int b) { return cherry_int_cmp(a, b) <= 0; }
static inline bool cherry_int_gt(cherry_int a, cherry_int b) { return cherry_int_cmp(a, b) > 0; }
static inline bool cherry_int_ge(cherry_int a, cherry_int b) { return cherry_int_cmp(a, b) >= 0; }

/* ------------------------------------------------------------------------
   Prims.string.  A cell with the byte size, the capacity of [data], and
   zero-terminated UTF-8.  Literals are static cells with a reference count
   of zero, which are never written to or freed. */

typedef cherry_obj *cherry_string;

typedef struct cherry_string_cell {
  cherry_obj hdr;
  size_t size;
  size_t cap;
  char data[];
} cherry_string_cell;

#if defined(__GNUC__)
#define CHERRY_UNUSED __attribute__((unused))
#else
#define CHERRY_UNUSED
#endif

#define CHERRY_STRING_LIT(name, s)                                         \
  static CHERRY_UNUSED struct { cherry_obj hdr; size_t size; size_t cap; char data[sizeof(s)]; } \
    name = { { 0, CHERRY_TAG_STRING }, sizeof(s) - 1, sizeof(s), s }

static inline const char *cherry_str_data(cherry_string s) {
  return ((cherry_string_cell *)s)->data;
}

static inline size_t cherry_str_size(cherry_string s) {
  return ((cherry_string_cell *)s)->size;
}

static inline bool cherry_str_eq(cherry_string a, cherry_string b) {
  return a == b ||
    (cherry_str_size(a) == cherry_str_size(b) &&
     memcmp(cherry_str_data(a), cherry_str_data(b), cherry_str_size(a)) == 0);
}

cherry_string cherry_str_of_bytes(const char *p, size_t n);
/* Takes [a] owned: a uniquely referenced [a] is extended in place. */
cherry_string cherry_str_append(cherry_string a, cherry_string b);
cherry_int cherry_str_length(cherry_string s);
uint32_t cherry_str_index(cherry_string s, cherry_int i);
cherry_string cherry_str_sub(cherry_string s, cherry_int i, cherry_int l);
cherry_int cherry_str_compare(cherry_string a, cherry_string b);
cherry_string cherry_string_of_int(cherry_int a);
void cherry_print_string(cherry_string s);

/* ------------------------------------------------------------------------
   Function values.  Every value of function type is a closure cell: the
   entry point, functions to drop and mark the captured values (NULL when
   there are none), the number of arguments the entry point takes, and then
   the captured values themselves.  The entry point is called as
   [R entry(cherry_fn self, A1 a1, ..., An an)] with [self] borrowed and the
   arguments owned; the generated [apply] helpers handle calls with fewer or
   more arguments than that.  A top-level function used as a value is a
   static closure with a reference count of zero. */

#define CHERRY_TAG_CLOSURE 0xFFFFFFF2u

typedef cherry_obj *cherry_fn;
/* The entry point, cast to the one function pointer type that every other
   one converts to and from without a warning. */
typedef void (*cherry_code)(void);

typedef struct cherry_closure {
  cherry_obj hdr;
  cherry_code fn;
  void (*drop)(cherry_obj *);
  void (*mark)(cherry_obj *);
  uint32_t arity;
} cherry_closure;

#define CHERRY_CLOSURE(f) ((cherry_closure *)(f))

#define CHERRY_STATIC_CLOSURE(name, code, n)                               \
  static CHERRY_UNUSED cherry_closure name =                               \
    { { 0, CHERRY_TAG_CLOSURE }, (cherry_code)(code), NULL, NULL, n }

static inline void cherry_dec_fn(cherry_fn f) {
  if (!cherry_dec_ref(f)) return;
  if (CHERRY_CLOSURE(f)->drop != NULL) CHERRY_CLOSURE(f)->drop(f);
  free(f);
}

static inline void cherry_mark_fn(cherry_fn f) {
  if (cherry_mark_ref(f) && CHERRY_CLOSURE(f)->mark != NULL)
    CHERRY_CLOSURE(f)->mark(f);
}

#ifdef __cplusplus
}
#endif

#endif
