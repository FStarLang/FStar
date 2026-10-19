/* Runtime support for F* code extracted with --codegen Cherry.
   See doc/ref/cherry.md in the F* repository.  Generated units include
   this header; put the directory $(fstar.exe --locate_lib)/ulib/c on the C
   include path.

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

/* The count of a shared cell is updated by other threads at the same time,
   so every access to a count is atomic.  Relaxed loads and stores are plain
   moves on x86 and ARM; they are only there to keep the program free of
   data races in the C11 sense (and quiet under ThreadSanitizer).  A count
   that is positive is this thread's alone, and stays so until this thread
   marks the cell, so it is read and written without read-modify-write. */
static inline int32_t cherry_rc_load(const cherry_obj *o) {
  return __atomic_load_n(&o->rc, __ATOMIC_RELAXED);
}

static inline void cherry_rc_store(cherry_obj *o, int32_t rc) {
  __atomic_store_n(&o->rc, rc, __ATOMIC_RELAXED);
}

/* Whether this thread holds the only reference, so that the cell can be
   updated or reused in place.  A shared or persistent cell never is. */
static inline bool cherry_is_unique(const cherry_obj *o) {
  return cherry_rc_load(o) == 1;
}

static inline cherry_obj *cherry_alloc(size_t size, uint32_t tag) {
  cherry_obj *o = (cherry_obj *)malloc(size);
  if (o == NULL) abort();
  cherry_rc_store(o, 1);
  o->tag = tag;
  return o;
}

static inline void cherry_inc(cherry_obj *o) {
  if (cherry_is_scalar(o)) return;
  int32_t rc = cherry_rc_load(o);
  if (rc > 0) cherry_rc_store(o, rc + 1);
  else if (rc < 0) __atomic_fetch_sub(&o->rc, 1, __ATOMIC_RELAXED);
}

/* Drop a reference; true when it was the last one and the cell has to be
   freed. */
static inline bool cherry_dec_ref(cherry_obj *o) {
  if (cherry_is_scalar(o)) return false;
  int32_t rc = cherry_rc_load(o);
  if (rc == 1) return true;
  if (rc > 1) { cherry_rc_store(o, rc - 1); return false; }
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
   marked too.  Only a cell of this thread's own (a positive count) changes.
   A shared one is left shared even when persisting: other threads may be
   counting it already, so zeroing its count would race with them.  It is
   kept alive all the same, by the reference the global never drops, and
   what it reaches is already shared. */
static inline bool cherry_mark_ref(cherry_obj *o, int mode) {
  if (cherry_is_scalar(o)) return false;
  int32_t rc = cherry_rc_load(o);
  if (rc <= 0) return false;
  cherry_rc_store(o, mode == CHERRY_PERSIST ? 0 : -rc);
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
/* Whether [a] is the integer literal [s] (a constant pattern too large to
   be a small integer), without keeping the literal. */
bool cherry_int_eq_decimal(cherry_int a, const char *s);
/* Conversions to and from the machine integers; [to] wraps modulo 2^64. */
cherry_int cherry_int_of_i64(int64_t v);
cherry_int cherry_int_of_u64(uint64_t v);
int64_t cherry_int_to_i64(cherry_int x);
uint64_t cherry_int_to_u64(cherry_int x);
#ifdef __SIZEOF_INT128__
/* The same at 128 bits, for --custard_int128; [to] wraps modulo 2^128. */
__extension__ typedef unsigned __int128 cherry_u128;
__extension__ typedef __int128 cherry_i128;
cherry_int cherry_int_of_i128(cherry_i128 v);
cherry_int cherry_int_of_u128(cherry_u128 v);
cherry_i128 cherry_int_to_i128(cherry_int x);
cherry_u128 cherry_int_to_u128(cherry_int x);
#endif

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
uint64_t cherry_str_fnv1a(cherry_string s);
/* Nanoseconds of the monotonic clock (FStarC.Timing). */
uint64_t cherry_now_ns(void);
/* Wall-clock nanoseconds since the Unix epoch (FStarC.Time). */
uint64_t cherry_wall_ns(void);
/* A file's modification time in nanoseconds since the epoch, UINT64_MAX
   when it cannot be read. */
uint64_t cherry_file_mtime_ns(cherry_string path);
/* [FStar.String.make l c]: [l] copies of the code point [c]. */
cherry_string cherry_str_make(cherry_int l, uint32_t c);
/* Byte-level access, for FStar.Pprint (whose lengths and offsets are in
   bytes, as in OCaml): the size in bytes, the byte at an offset (0 past the
   end), and the bytes [off, off + len), clamped to the string. */
cherry_int cherry_str_byte_size(cherry_string s);
uint32_t cherry_str_byte_at(cherry_string s, cherry_int off);
cherry_string cherry_str_byte_sub(cherry_string s, cherry_int off, cherry_int len);

/* FStar.Char: a char is its code point. */
static inline uint32_t cherry_u32_of_char(uint32_t c) { return c; }
static inline uint32_t cherry_char_of_u32(uint32_t c) { return c; }
cherry_string cherry_string_of_int(cherry_int a);
cherry_string cherry_string_of_bool(bool b);
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
   Pulse references and arrays of counted values (cherry.md,
   "References").  They are not counted themselves: Pulse's permissions say
   who may read, write and free one.  What they hold is, and is marked shared
   when it is stored, since a Pulse container may be read from several
   threads at once.  A heap allocation keeps its length in a header in front
   of the elements, so that freeing it can release them; the generated
   helpers (cherry_pbuf<N>_alloc/read/write/free/init/drop/blit) do the
   rest. */

typedef union cherry_pbuf_hdr { size_t n; long double d; void *p; } cherry_pbuf_hdr;

static inline void *cherry_pbuf_new(size_t n, size_t size) {
  if (size != 0 && n > (SIZE_MAX - sizeof(cherry_pbuf_hdr)) / size) abort();
  cherry_pbuf_hdr *h = (cherry_pbuf_hdr *)malloc(sizeof(cherry_pbuf_hdr) + n * size);
  if (h == NULL) abort();
  h->n = n;
  return (void *)(h + 1);
}

static inline size_t cherry_pbuf_len(void *b) { return ((cherry_pbuf_hdr *)b - 1)->n; }

static inline void cherry_pbuf_release(void *b) { free((cherry_pbuf_hdr *)b - 1); }

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

/* Every unit that raises or matches an exception has its own copy of its
   info, so identity is the name, which is the F* name and so unique in the
   program; the pointer comparison is the fast path within a unit. */
static inline bool cherry_exn_is(cherry_exn e, const cherry_exn_info *info) {
  const cherry_exn_info *have = ((cherry_exn_hdr *)e)->info;
  return have == info || strcmp(have->name, info->name) == 0;
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
   The any type (cherry.md, "The any type"): [FStar.Dyn.dyn].  A word and
   the type information that says how to count and mark it.  A value that
   fits in the word is stored in it; a larger one is boxed in a counted cell
   (CHERRY_TAG_ANY), which the word points to.  A plain type has no
   operations.  The type information is generated, one per type. */

#define CHERRY_TAG_ANY 0xFFFFFFF5u

typedef struct cherry_rtti {
  const char *name;
  void (*inc)(uintptr_t);
  void (*dec)(uintptr_t);
  void (*mark)(uintptr_t, int);
} cherry_rtti;

typedef struct cherry_any { uintptr_t v; const cherry_rtti *rtti; } cherry_any;

static inline void cherry_any_inc(cherry_any a) { if (a.rtti->inc) a.rtti->inc(a.v); }
static inline void cherry_any_dec(cherry_any a) { if (a.rtti->dec) a.rtti->dec(a.v); }
static inline void cherry_any_mark(cherry_any a, int mode) { if (a.rtti->mark) a.rtti->mark(a.v, mode); }

/* [undyn] where the type information is not this unit's for the type:
   another unit's for the same type, which is identified by its C name (the
   payload layout is the same), or a mismatch, which aborts. */
void cherry_any_mismatch(const cherry_rtti *have, const char *want);

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

/* The arity of a closure that has only unit parameters left and returns a
   value: it runs when the type it is applied at has no arrow left. */
#define CHERRY_ARITY_UNITS 0x7fffffffu

#define CHERRY_STATIC_CLOSURE(name, code, n)                               \
  static CHERRY_UNUSED cherry_closure name =                               \
    { { 0, CHERRY_TAG_CLOSURE }, (cherry_code)(code), NULL, NULL, n }

void cherry_free_closure(cherry_obj *f, int mode);

/* A static closure is persistent, so it never reaches [free]; GCC cannot
   tell once it inlines one into this. */
#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wfree-nonheap-object"
#endif
static inline void cherry_dec_fn(cherry_fn f) {
  if (!cherry_dec_ref(f)) return;
  if (CHERRY_CLOSURE(f)->drop != NULL) cherry_defer(f, cherry_free_closure, 0);
  else free(f);
}
#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic pop
#endif

static inline void cherry_mark_fn(cherry_fn f, int mode) {
  if (cherry_mark_ref(f, mode) && CHERRY_CLOSURE(f)->mark != NULL)
    cherry_defer(f, CHERRY_CLOSURE(f)->mark, mode);
}

#ifndef CUSTARD_UNIT_DEFINED
#define CUSTARD_UNIT_DEFINED
typedef uint8_t custard_unit;
#endif

/* Run a closure of type [unit -> unit] from hand-written C: how a
   realization (a thread's body, say) calls back into F*.  Borrows [f].  An
   exception that escapes it is uncaught. */
static inline void cherry_call_thunk(cherry_fn f) {
  uint32_t a = CHERRY_CLOSURE(f)->arity;
  if (a != 0 && a != CHERRY_ARITY_UNITS) abort();
  (void)((custard_unit (*)(cherry_fn))CHERRY_CLOSURE(f)->fn)(f);
  if (CHERRY_EXN_PENDING()) cherry_exn_uncaught();
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
