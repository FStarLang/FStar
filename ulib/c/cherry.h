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
#include <stddef.h>

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

/* Marking walks everything a value reaches, in one of two modes: making it
   shared between threads (a negative reference count, updated atomically),
   or making it persistent (a reference count of zero: never updated and
   never freed), which is what a global's value is once it is computed. */
#define CHERRY_SHARE 0
#define CHERRY_PERSIST 1

/* Mark a cell; true when that changed it, so that its fields have to be
   marked too. */
static inline bool cherry_mark_ref(cherry_obj *o, int mode) {
  if (cherry_is_scalar(o) || o->rc == 0) return false;
  if (mode == CHERRY_PERSIST) { o->rc = 0; return true; }
  if (o->rc < 0) return false;
  o->rc = -o->rc;
  return true;
}

/* Cells allocated by the runtime itself, which have no counted fields. */
#define CHERRY_TAG_BIGINT 0xFFFFFFF0u
#define CHERRY_TAG_STRING 0xFFFFFFF1u

/* Freeing and marking walk values of any depth without recursing on the C
   stack.  The generated [dec] and [mark] of a type hand the cell whose
   fields have to be visited to [cherry_defer], with the function that
   visits them: it runs at once, unless a walk is already under way on this
   thread, in which case it joins that walk's work list.  A visit function
   follows a field of its own type in a loop, so a list's spine never
   reaches the work list. */
typedef void (*cherry_work_fn)(cherry_obj *, int);
void cherry_defer(cherry_obj *o, cherry_work_fn f, int mode);

static inline void cherry_dec(cherry_obj *o) {
  if (cherry_dec_ref(o)) free(o);
}

static inline void cherry_mark(cherry_obj *o, int mode) {
  (void)cherry_mark_ref(o, mode);
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
   Immutable arrays (FStar.ImmutableArray.t).  A cell with the number of
   elements, the capacity, and then the elements; the generated code defines
   the cell for each element type and the operations on it
   (cherry_iarr<N>_of_list/to_list/index/upd/push/dec/mark).  An update or a
   push changes a uniquely referenced array in place, as an append does a
   string, and copies any other. */

#define CHERRY_TAG_IARRAY 0xFFFFFFF3u

typedef cherry_obj *cherry_iarray;

typedef struct cherry_iarray_hdr { cherry_obj hdr; size_t size; size_t cap; } cherry_iarray_hdr;

static inline cherry_int cherry_iarray_length(cherry_iarray a) {
  return CHERRY_INT_SMALL(((cherry_iarray_hdr *)a)->size);
}

/* An index, which F* has checked is a natural number below the length, so
   it is a small integer. */
static inline size_t cherry_iarray_pos(cherry_int i) {
  return (size_t)cherry_int_val(i);
}

/* ------------------------------------------------------------------------
   Exceptions (cherry.md, "Exceptions"), as error returns.  [raise] stores
   the exception in a thread-local slot and returns; every call that may
   raise is followed by a test of the slot, which on a pending exception
   releases what the caller holds and returns in turn, and a [try] takes it
   out again.  An exception is a cell whose constructor is told by its
   [cherry_exn_info], which also says how to free and mark its fields: the
   type is open, so no switch on a tag could. */

#ifdef __cplusplus
#define CHERRY_THREAD_LOCAL thread_local
#else
#define CHERRY_THREAD_LOCAL _Thread_local
#endif

#define CHERRY_TAG_EXN 0xFFFFFFF4u

typedef cherry_obj *cherry_exn;

typedef struct cherry_exn_info {
  const char *name;
  cherry_work_fn free;
  cherry_work_fn mark;
  /* The offset of a string field to report if the exception escapes, as
     for [Failure]; 0 if there is none. */
  size_t msg;
} cherry_exn_info;

typedef struct cherry_exn_hdr { cherry_obj hdr; const cherry_exn_info *info; } cherry_exn_hdr;

extern CHERRY_THREAD_LOCAL cherry_exn cherry_exn_slot;

static inline void cherry_raise(cherry_exn e) { cherry_exn_slot = e; }

#define CHERRY_EXN_PENDING() __builtin_expect(cherry_exn_slot != NULL, 0)

static inline cherry_exn cherry_exn_take(void) {
  cherry_exn e = cherry_exn_slot;
  cherry_exn_slot = NULL;
  return e;
}

static inline bool cherry_exn_is(cherry_exn e, const cherry_exn_info *info) {
  return ((cherry_exn_hdr *)e)->info == info;
}

static inline void cherry_exn_dec(cherry_exn e) {
  if (cherry_dec_ref(e)) cherry_defer(e, ((cherry_exn_hdr *)e)->info->free, 0);
}

static inline void cherry_exn_mark(cherry_exn e, int mode) {
  if (cherry_mark_ref(e, mode)) cherry_defer(e, ((cherry_exn_hdr *)e)->info->mark, mode);
}

/* An exception nothing caught: reported, and the process exits. */
void cherry_exn_uncaught(void);

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
  void (*mark)(cherry_obj *, int);
  uint32_t arity;
} cherry_closure;

#define CHERRY_CLOSURE(f) ((cherry_closure *)(f))

#define CHERRY_STATIC_CLOSURE(name, code, n)                               \
  static CHERRY_UNUSED cherry_closure name =                               \
    { { 0, CHERRY_TAG_CLOSURE }, (cherry_code)(code), NULL, NULL, n }

void cherry_free_closure(cherry_obj *f, int mode);

static inline void cherry_dec_fn(cherry_fn f) {
  if (!cherry_dec_ref(f)) return;
  if (CHERRY_CLOSURE(f)->drop != NULL) cherry_defer(f, cherry_free_closure, 0);
  else free(f);
}

static inline void cherry_mark_fn(cherry_fn f, int mode) {
  if (cherry_mark_ref(f, mode) && CHERRY_CLOSURE(f)->mark != NULL)
    cherry_defer(f, CHERRY_CLOSURE(f)->mark, mode);
}

/* ------------------------------------------------------------------------
   ML references (FStar.All.ref, FStarC.Effect.ref).  A counted cell holding
   a spinlock and the value; the generated code defines the cell for each
   value type and the operations on it (cherry_ref<N>_new/get/set/dec/mark).
   While the cell is reachable from one thread only, reads and writes leave
   the lock alone.  Otherwise -- shared, or persistent, since a global is
   reachable from every thread -- they hold the lock while they copy the
   value and count the copy, so that a writer cannot free the old value
   before a reader has taken its reference to it, and the value written is
   marked shared first. */
typedef cherry_obj *cherry_ref;

typedef struct cherry_ref_hdr { cherry_obj hdr; int32_t lock; } cherry_ref_hdr;

static inline bool cherry_ref_is_local(cherry_ref r) {
  return __atomic_load_n(&r->rc, __ATOMIC_RELAXED) > 0;
}

static inline void cherry_ref_lock(cherry_ref r) {
  int32_t *l = &((cherry_ref_hdr *)r)->lock;
  while (__atomic_exchange_n(l, 1, __ATOMIC_ACQUIRE))
    while (__atomic_load_n(l, __ATOMIC_RELAXED)) {}
}

static inline void cherry_ref_unlock(cherry_ref r) {
  __atomic_store_n(&((cherry_ref_hdr *)r)->lock, 0, __ATOMIC_RELEASE);
}

#ifdef __cplusplus
}
#endif

#endif
