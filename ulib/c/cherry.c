/* Slow paths of the Cherry runtime: deferred work, big integers and strings.  See cherry.h.

   Big integers are sign and magnitude, the magnitude in 32-bit limbs, least
   significant first, with no leading zero limbs.  A result that fits in a
   small integer is always returned as one. */
#define _XOPEN_SOURCE 700 /* clock_gettime, getline, realpath, posix_spawn */
#if defined(__APPLE__)
#define _DARWIN_C_SOURCE /* _NSGetExecutablePath */
#endif
#include "cherry.h"

#include <inttypes.h>
#include <stdio.h>
#include <time.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <poll.h>
#include <signal.h>
#include <spawn.h>
#include <sys/stat.h>
#include <sys/utsname.h>
#include <sys/wait.h>
#include <unistd.h>
#if defined(__APPLE__)
#include <mach-o/dyld.h>
#endif

/* ------------------------------------------------------------------------
   Deferred work (cherry.h): one work list per thread, kept between walks. */

typedef struct { cherry_obj *o; cherry_work_fn f; int mode; } job;

static _Thread_local job *jobs;
static _Thread_local size_t njobs, cap;
static _Thread_local bool busy;

_Thread_local cherry_exn cherry_exn_slot;

void cherry_any_mismatch(const cherry_rtti *have, const char *want) {
  if (strcmp(have->name, want) == 0) return;
  fflush(stdout);
  fprintf(stderr, "undyn: a value of type %s read at type %s\n", have->name, want);
  abort();
}

void cherry_debug_fail(const char *what, const char *file, int line) {
  fflush(stdout);
  fprintf(stderr, "%s:%d: Cherry debug check failed: %s\n", file, line, what);
  abort();
}

void cherry_exn_uncaught(void) {
  cherry_exn e = cherry_exn_take();
  fflush(stdout);
  const cherry_exn_info *info = ((cherry_exn_hdr *)e)->info;
  if (info->msg != 0)
    fprintf(stderr, "Uncaught exception: %s(\"%s\")\n", info->name,
            cherry_str_data(*(cherry_string *)((char *)e + info->msg)));
  else
    fprintf(stderr, "Uncaught exception: %s\n", info->name);
  cherry_exn_dec(e);
  exit(2);
}

void cherry_exit(cherry_int n) {
  fflush(stdout);
  fflush(stderr);
  exit((int)cherry_int_to_i64(n));
}

void cherry_defer(cherry_obj *o, cherry_work_fn f, int mode) {
  if (busy) {
    if (njobs == cap) {
      cap = cap == 0 ? 64 : 2 * cap;
      jobs = (job *)realloc(jobs, cap * sizeof(job));
      if (jobs == NULL) abort();
    }
    jobs[njobs++] = (job){ o, f, mode };
    return;
  }
  busy = true;
  f(o, mode);
  while (njobs > 0) {
    job j = jobs[--njobs];
    j.f(j.o, j.mode);
  }
  busy = false;
}

void cherry_free_closure(cherry_obj *f, int mode) {
  (void)mode;
  CHERRY_CLOSURE(f)->drop(f);
  free(f);
}

/* A big integer cell: sign and magnitude, in 32-bit limbs, least
   significant first.  CHERRY_INT_LIT (cherry.h) builds one statically. */
typedef struct cherry_bigint {
  cherry_obj hdr;
  uint32_t neg;
  uint32_t len;
  uint32_t d[];
} cherry_bigint;

/* A read-only view of either representation. */
typedef struct {
  bool neg;
  uint32_t len;
  const uint32_t *d;
  uint32_t buf[2];
} view;

static void view_of(cherry_int a, view *v) {
  if (cherry_is_scalar(a)) {
    int64_t x = (int64_t)cherry_int_val(a);
    uint64_t m = x < 0 ? (uint64_t)0 - (uint64_t)x : (uint64_t)x;
    v->neg = x < 0;
    v->buf[0] = (uint32_t)m;
    v->buf[1] = (uint32_t)(m >> 32);
    v->len = m == 0 ? 0 : (v->buf[1] != 0 ? 2 : 1);
    v->d = v->buf;
  } else {
    const cherry_bigint *b = (const cherry_bigint *)a;
    v->neg = b->neg != 0;
    v->len = b->len;
    v->d = b->d;
  }
}

static void *xmalloc(size_t n) {
  void *p = malloc(n == 0 ? 1 : n);
  if (p == NULL) abort();
  return p;
}

/* Strip leading zeros; demote to a small integer when it fits. */
static cherry_int big_finish(cherry_bigint *b) {
  uint32_t n = b->len;
  while (n > 0 && b->d[n - 1] == 0) n--;
  b->len = n;
  if (n <= 2) {
    uint64_t m = n == 0 ? 0 : n == 1 ? b->d[0]
               : ((uint64_t)b->d[1] << 32) | b->d[0];
    uint64_t lim = (uint64_t)CHERRY_INT_MAX + (b->neg ? 1u : 0u);
    if (m <= lim) {
      intptr_t x = m == 0 ? 0
                 : b->neg ? (intptr_t)(-(int64_t)(m - 1) - 1)
                 : (intptr_t)m;
      free(b);
      return CHERRY_INT_SMALL(x);
    }
  }
  return (cherry_int)b;
}

static cherry_int big_from(bool neg, const uint32_t *d, uint32_t len) {
  cherry_bigint *b = (cherry_bigint *)cherry_alloc(
      sizeof(cherry_bigint) + sizeof(uint32_t) * (size_t)len, CHERRY_TAG_BIGINT);
  b->neg = neg;
  b->len = len;
  if (len) memcpy(b->d, d, sizeof(uint32_t) * (size_t)len);
  return big_finish(b);
}

/* ---- magnitudes ---- */

static int mag_cmp(const uint32_t *a, uint32_t la, const uint32_t *b, uint32_t lb) {
  if (la != lb) return la < lb ? -1 : 1;
  for (uint32_t i = la; i-- > 0;)
    if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
  return 0;
}

/* out[0..la] = a + b, la >= lb. */
static void mag_add(const uint32_t *a, uint32_t la, const uint32_t *b, uint32_t lb,
                    uint32_t *out) {
  uint64_t c = 0;
  for (uint32_t i = 0; i < la; i++) {
    c += (uint64_t)a[i] + (i < lb ? b[i] : 0);
    out[i] = (uint32_t)c;
    c >>= 32;
  }
  out[la] = (uint32_t)c;
}

/* out[0..la) = a - b, a >= b. */
static void mag_sub(const uint32_t *a, uint32_t la, const uint32_t *b, uint32_t lb,
                    uint32_t *out) {
  int64_t c = 0;
  for (uint32_t i = 0; i < la; i++) {
    c += (int64_t)a[i] - (i < lb ? (int64_t)b[i] : 0);
    out[i] = (uint32_t)c;
    c = c < 0 ? -1 : 0;
  }
}

/* Knuth, TAOCP vol. 2, 4.3.1, algorithm D (after Hacker's Delight, divmnu).
   u has m limbs, v has n limbs with v[n-1] != 0, m >= n.  q gets m-n+1
   limbs, r gets n. */
static void mag_divmod(const uint32_t *u, uint32_t m, const uint32_t *v, uint32_t n,
                       uint32_t *q, uint32_t *r) {
  const uint64_t b = (uint64_t)1 << 32;
  if (n == 1) {
    uint64_t k = 0;
    for (uint32_t j = m; j-- > 0;) {
      uint64_t cur = (k << 32) | u[j];
      q[j] = (uint32_t)(cur / v[0]);
      k = cur % v[0];
    }
    r[0] = (uint32_t)k;
    return;
  }
  int s = __builtin_clz(v[n - 1]);
  uint32_t *vn = (uint32_t *)xmalloc(sizeof(uint32_t) * n);
  uint32_t *un = (uint32_t *)xmalloc(sizeof(uint32_t) * (m + 1));
  for (uint32_t i = n - 1; i > 0; i--)
    vn[i] = (v[i] << s) | (s ? (uint32_t)((uint64_t)v[i - 1] >> (32 - s)) : 0);
  vn[0] = v[0] << s;
  un[m] = s ? (uint32_t)((uint64_t)u[m - 1] >> (32 - s)) : 0;
  for (uint32_t i = m - 1; i > 0; i--)
    un[i] = (u[i] << s) | (s ? (uint32_t)((uint64_t)u[i - 1] >> (32 - s)) : 0);
  un[0] = u[0] << s;
  for (uint32_t j = m - n + 1; j-- > 0;) {
    uint64_t num = ((uint64_t)un[j + n] << 32) | un[j + n - 1];
    uint64_t qhat = num / vn[n - 1];
    uint64_t rhat = num % vn[n - 1];
    while (qhat >= b || qhat * vn[n - 2] > ((rhat << 32) | un[j + n - 2])) {
      qhat--;
      rhat += vn[n - 1];
      if (rhat >= b) break;
    }
    int64_t k = 0, t;
    for (uint32_t i = 0; i < n; i++) {
      uint64_t p = qhat * vn[i];
      t = (int64_t)un[i + j] - k - (int64_t)(p & 0xFFFFFFFFu);
      un[i + j] = (uint32_t)t;
      k = (int64_t)(p >> 32) - (t >> 32);
    }
    t = (int64_t)un[j + n] - k;
    un[j + n] = (uint32_t)t;
    q[j] = (uint32_t)qhat;
    if (t < 0) {
      q[j]--;
      uint64_t c = 0;
      for (uint32_t i = 0; i < n; i++) {
        c += (uint64_t)un[i + j] + vn[i];
        un[i + j] = (uint32_t)c;
        c >>= 32;
      }
      un[j + n] += (uint32_t)c;
    }
  }
  for (uint32_t i = 0; i + 1 < n; i++)
    r[i] = (un[i] >> s) | (s ? (uint32_t)((uint64_t)un[i + 1] << (32 - s)) : 0);
  r[n - 1] = un[n - 1] >> s;
  free(vn);
  free(un);
}

/* ---- signed operations ---- */

static cherry_int big_addsub(cherry_int x, cherry_int y, bool sub) {
  view a, b;
  view_of(x, &a);
  view_of(y, &b);
  bool bneg = b.neg != sub;
  if (a.neg == bneg) {
    const view *p = a.len >= b.len ? &a : &b, *q = a.len >= b.len ? &b : &a;
    uint32_t *t = (uint32_t *)xmalloc(sizeof(uint32_t) * (p->len + 1));
    mag_add(p->d, p->len, q->d, q->len, t);
    cherry_int r = big_from(a.neg, t, p->len + 1);
    free(t);
    return r;
  }
  int c = mag_cmp(a.d, a.len, b.d, b.len);
  if (c == 0) return CHERRY_INT_SMALL(0);
  const view *p = c > 0 ? &a : &b, *q = c > 0 ? &b : &a;
  uint32_t *t = (uint32_t *)xmalloc(sizeof(uint32_t) * p->len);
  mag_sub(p->d, p->len, q->d, q->len, t);
  cherry_int r = big_from(c > 0 ? a.neg : bneg, t, p->len);
  free(t);
  return r;
}

cherry_int cherry_big_add(cherry_int a, cherry_int b) { return big_addsub(a, b, false); }
cherry_int cherry_big_sub(cherry_int a, cherry_int b) { return big_addsub(a, b, true); }

cherry_int cherry_big_mul(cherry_int x, cherry_int y) {
  view a, b;
  view_of(x, &a);
  view_of(y, &b);
  if (a.len == 0 || b.len == 0) return CHERRY_INT_SMALL(0);
  uint32_t n = a.len + b.len;
  uint32_t *t = (uint32_t *)xmalloc(sizeof(uint32_t) * n);
  memset(t, 0, sizeof(uint32_t) * n);
  for (uint32_t i = 0; i < a.len; i++) {
    uint64_t c = 0;
    for (uint32_t j = 0; j < b.len; j++) {
      c += (uint64_t)a.d[i] * b.d[j] + t[i + j];
      t[i + j] = (uint32_t)c;
      c >>= 32;
    }
    t[i + b.len] = (uint32_t)c;
  }
  cherry_int r = big_from(a.neg != b.neg, t, n);
  free(t);
  return r;
}

/* Euclidean quotient and remainder; either pointer may be NULL. */
static void big_edivmod(cherry_int x, cherry_int y, cherry_int *qo, cherry_int *ro) {
  view a, b;
  view_of(x, &a);
  view_of(y, &b);
  if (b.len == 0) abort();
  uint32_t ql = a.len >= b.len ? a.len - b.len + 1 : 0;
  uint32_t *q = (uint32_t *)xmalloc(sizeof(uint32_t) * (ql + 1));
  uint32_t *r = (uint32_t *)xmalloc(sizeof(uint32_t) * (a.len > b.len ? a.len : b.len));
  uint32_t rl;
  if (mag_cmp(a.d, a.len, b.d, b.len) < 0) {
    ql = 0;
    rl = a.len;
    if (rl) memcpy(r, a.d, sizeof(uint32_t) * rl);
  } else {
    mag_divmod(a.d, a.len, b.d, b.len, q, r);
    rl = b.len;
  }
  while (rl > 0 && r[rl - 1] == 0) rl--;
  /* Truncated division gives a remainder with the sign of [a]; a negative
     one is moved up by |b|, and the quotient one further from zero. */
  if (a.neg && rl > 0) {
    uint32_t *t = (uint32_t *)xmalloc(sizeof(uint32_t) * b.len);
    mag_sub(b.d, b.len, r, rl, t);
    memcpy(r, t, sizeof(uint32_t) * b.len);
    rl = b.len;
    free(t);
    uint64_t c = 1;
    for (uint32_t i = 0; i < ql && c; i++) {
      c += q[i];
      q[i] = (uint32_t)c;
      c >>= 32;
    }
    if (c) q[ql++] = (uint32_t)c;
    if (ql == 0) { q[0] = 1; ql = 1; }
    if (qo) *qo = big_from(a.neg != b.neg, q, ql);
    if (ro) *ro = big_from(false, r, rl);
  } else {
    if (qo) *qo = big_from(a.neg != b.neg, q, ql);
    if (ro) *ro = big_from(false, r, rl);
  }
  free(q);
  free(r);
}

cherry_int cherry_big_ediv(cherry_int a, cherry_int b) {
  /* A small dividend has the smaller magnitude: the quotient is 0, or the
     one of -1 and 1 that makes the remainder non-negative. */
  if (cherry_is_scalar(a) && !cherry_is_scalar(b)) {
    if (cherry_int_val(a) >= 0) return CHERRY_INT_SMALL(0);
    return CHERRY_INT_SMALL(((const cherry_bigint *)b)->neg ? 1 : -1);
  }
  cherry_int q;
  big_edivmod(a, b, &q, NULL);
  return q;
}

cherry_int cherry_big_erem(cherry_int a, cherry_int b) {
  /* A small dividend over a big divisor: the quotient is 0 or +-1 (see
     cherry_big_ediv), so the remainder is [a] or [a + |b|]. */
  if (cherry_is_scalar(a) && !cherry_is_scalar(b) && cherry_int_val(a) < 0)
    return ((const cherry_bigint *)b)->neg ? cherry_int_sub(a, b) : cherry_int_add(a, b);
  cherry_int r;
  big_edivmod(a, b, NULL, &r);
  return r;
}

cherry_int cherry_big_neg(cherry_int x) {
  view a;
  view_of(x, &a);
  return big_from(!a.neg, a.d, a.len);
}

int cherry_big_cmp(cherry_int x, cherry_int y) {
  view a, b;
  view_of(x, &a);
  view_of(y, &b);
  if (a.neg != b.neg) return a.neg ? -1 : 1;
  int c = mag_cmp(a.d, a.len, b.d, b.len);
  return a.neg ? -c : c;
}

cherry_int cherry_int_of_decimal(const char *s) {
  bool neg = false;
  if (*s == '-') { neg = true; s++; }
  size_t n = strlen(s);
  uint32_t cap = (uint32_t)(n / 9 + 2), len = 0;
  uint32_t *d = (uint32_t *)xmalloc(sizeof(uint32_t) * cap);
  for (size_t i = 0; i < n;) {
    uint32_t chunk = 0, mul = 1;
    for (int k = 0; k < 9 && i < n; k++, i++) {
      chunk = chunk * 10 + (uint32_t)(s[i] - '0');
      mul *= 10;
    }
    uint64_t c = chunk;
    for (uint32_t j = 0; j < len; j++) {
      c += (uint64_t)d[j] * mul;
      d[j] = (uint32_t)c;
      c >>= 32;
    }
    if (c) d[len++] = (uint32_t)c;
  }
  cherry_int r = big_from(neg, d, len);
  free(d);
  return r;
}

/* ---- strings ---- */

static cherry_string_cell *str_alloc(size_t size, size_t cap) {
  cherry_string_cell *c = (cherry_string_cell *)cherry_alloc(
      sizeof(cherry_string_cell) + cap, CHERRY_TAG_STRING);
  c->size = size;
  c->cap = cap;
  c->data[size] = 0;
  return c;
}

cherry_string cherry_str_of_bytes(const char *p, size_t n) {
  cherry_string_cell *c = str_alloc(n, n + 1);
  if (n) memcpy(c->data, p, n);
  return (cherry_string)c;
}

cherry_string cherry_str_append(cherry_string a, cherry_string b) {
  cherry_string_cell *x = (cherry_string_cell *)a;
  const cherry_string_cell *y = (const cherry_string_cell *)b;
  size_t ys = y->size, n = x->size + ys;
  if (cherry_is_unique(&x->hdr)) {
    /* Functional but in place: nobody else can see [a] -- except [b], which
       may be [a] itself, borrowed, and moves with it. */
    bool same = x == y;
    if (n + 1 > x->cap) {
      size_t cap = 2 * n + 1;
      x = (cherry_string_cell *)realloc(x, sizeof(cherry_string_cell) + cap);
      if (x == NULL) abort();
      x->cap = cap;
    }
    memmove(x->data + x->size, same ? x->data : y->data, ys);
    x->size = n;
    x->data[n] = 0;
    return (cherry_string)x;
  }
  cherry_string_cell *c = str_alloc(n, n + 1);
  memcpy(c->data, x->data, x->size);
  memcpy(c->data + x->size, y->data, y->size);
  cherry_dec(a);
  return (cherry_string)c;
}

/* The byte offset of code point [i], or the size if there are fewer. */
static size_t cp_offset(const cherry_string_cell *c, size_t i) {
  size_t off = 0;
  while (off < c->size) {
    if (((unsigned char)c->data[off] & 0xC0) != 0x80) {
      if (i == 0) return off;
      i--;
    }
    off++;
  }
  return off;
}

static size_t int_index(cherry_int i) {
  if (!cherry_is_scalar(i) || cherry_int_val(i) < 0) abort();
  return (size_t)cherry_int_val(i);
}

cherry_int cherry_str_length(cherry_string s) {
  const cherry_string_cell *c = (const cherry_string_cell *)s;
  intptr_t n = 0;
  for (size_t i = 0; i < c->size; i++)
    if (((unsigned char)c->data[i] & 0xC0) != 0x80) n++;
  return CHERRY_INT_SMALL(n);
}

uint32_t cherry_str_index(cherry_string s, cherry_int i) {
  const cherry_string_cell *c = (const cherry_string_cell *)s;
  size_t off = cp_offset(c, int_index(i));
  if (off >= c->size) abort();
  const unsigned char *p = (const unsigned char *)c->data + off;
  if (p[0] < 0x80) return p[0];
  /* A sequence cut short by the end of the string is not read past it. */
  size_t len = p[0] < 0xE0 ? 2 : p[0] < 0xF0 ? 3 : 4;
  if (len > c->size - off) return 0xFFFD;
  if (p[0] < 0xE0) return ((uint32_t)(p[0] & 0x1F) << 6) | (p[1] & 0x3F);
  if (p[0] < 0xF0)
    return ((uint32_t)(p[0] & 0x0F) << 12) | ((uint32_t)(p[1] & 0x3F) << 6) | (p[2] & 0x3F);
  return ((uint32_t)(p[0] & 0x07) << 18) | ((uint32_t)(p[1] & 0x3F) << 12) |
         ((uint32_t)(p[2] & 0x3F) << 6) | (p[3] & 0x3F);
}

cherry_string cherry_str_sub(cherry_string s, cherry_int i, cherry_int l) {
  const cherry_string_cell *c = (const cherry_string_cell *)s;
  size_t start = cp_offset(c, int_index(i));
  size_t len = int_index(l), end = start;
  while (end < c->size && len > 0) {
    end++;
    while (end < c->size && ((unsigned char)c->data[end] & 0xC0) == 0x80) end++;
    len--;
  }
  return cherry_str_of_bytes(c->data + start, end - start);
}

cherry_string cherry_str_make(cherry_int l, uint32_t c) {
  unsigned char enc[4];
  size_t w;
  if (c < 0x80) { enc[0] = (unsigned char)c; w = 1; }
  else if (c < 0x800) {
    enc[0] = (unsigned char)(0xC0 | (c >> 6));
    enc[1] = (unsigned char)(0x80 | (c & 0x3F)); w = 2;
  } else if (c < 0x10000) {
    enc[0] = (unsigned char)(0xE0 | (c >> 12));
    enc[1] = (unsigned char)(0x80 | ((c >> 6) & 0x3F));
    enc[2] = (unsigned char)(0x80 | (c & 0x3F)); w = 3;
  } else {
    enc[0] = (unsigned char)(0xF0 | (c >> 18));
    enc[1] = (unsigned char)(0x80 | ((c >> 12) & 0x3F));
    enc[2] = (unsigned char)(0x80 | ((c >> 6) & 0x3F));
    enc[3] = (unsigned char)(0x80 | (c & 0x3F)); w = 4;
  }
  size_t n = int_index(l);
  cherry_string_cell *r = str_alloc(n * w, n * w + 1);
  for (size_t i = 0; i < n; i++) memcpy(r->data + i * w, enc, w);
  return (cherry_string)r;
}

cherry_int cherry_str_byte_size(cherry_string s) {
  return CHERRY_INT_SMALL((intptr_t)cherry_str_size(s));
}

uint32_t cherry_str_byte_at(cherry_string s, cherry_int off) {
  size_t i = int_index(off);
  return i < cherry_str_size(s) ? (unsigned char)cherry_str_data(s)[i] : 0;
}

cherry_string cherry_str_byte_sub(cherry_string s, cherry_int off, cherry_int len) {
  size_t size = cherry_str_size(s), i = int_index(off), n = int_index(len);
  if (i > size) i = size;
  if (n > size - i) n = size - i;
  return cherry_str_of_bytes(cherry_str_data(s) + i, n);
}

uint64_t cherry_str_size64(cherry_string s) {
  return (uint64_t)cherry_str_size(s);
}

uint64_t cherry_str_byte_at64(cherry_string s, uint64_t i) {
  return (int64_t)i >= 0 && i < cherry_str_size(s)
    ? (unsigned char)cherry_str_data(s)[i] : UINT64_MAX;
}

cherry_string cherry_str_slice64(cherry_string s, uint64_t i, uint64_t j) {
  int64_t n = (int64_t)cherry_str_size(s), a = (int64_t)i, b = (int64_t)j;
  if (a < 0) a = 0;
  if (b > n) b = n;
  if (b <= a) return cherry_str_of_bytes("", 0);
  return cherry_str_of_bytes(cherry_str_data(s) + a, (size_t)(b - a));
}

cherry_string cherry_str_of_byte(uint32_t b) {
  char c = (char)(unsigned char)b;
  return cherry_str_of_bytes(&c, 1);
}

static cherry_string str_map_ascii(cherry_string s, char lo, char hi, int d) {
  size_t n = cherry_str_size(s);
  cherry_string_cell *c = str_alloc(n, n + 1);
  const char *p = cherry_str_data(s);
  for (size_t i = 0; i < n; i++)
    c->data[i] = (char)(p[i] >= lo && p[i] <= hi ? p[i] + d : p[i]);
  return (cherry_string)c;
}

cherry_string cherry_str_lowercase_ascii(cherry_string s) {
  return str_map_ascii(s, 'A', 'Z', 'a' - 'A');
}

cherry_string cherry_str_uppercase_ascii(cherry_string s) {
  return str_map_ascii(s, 'a', 'z', 'A' - 'a');
}

cherry_string cherry_str_escaped(cherry_string s) {
  const unsigned char *p = (const unsigned char *)cherry_str_data(s);
  size_t n = cherry_str_size(s), m = 0;
  for (size_t i = 0; i < n; i++)
    m += strchr("\\\"\n\t\r\b", p[i]) && p[i] ? 2 : p[i] >= 32 && p[i] < 127 ? 1 : 4;
  cherry_string_cell *c = str_alloc(m, m + 1);
  char *q = c->data;
  for (size_t i = 0; i < n; i++) {
    unsigned char b = p[i];
    switch (b) {
    case '\\': *q++ = '\\'; *q++ = '\\'; break;
    case '"': *q++ = '\\'; *q++ = '"'; break;
    case '\n': *q++ = '\\'; *q++ = 'n'; break;
    case '\t': *q++ = '\\'; *q++ = 't'; break;
    case '\r': *q++ = '\\'; *q++ = 'r'; break;
    case '\b': *q++ = '\\'; *q++ = 'b'; break;
    default:
      if (b >= 32 && b < 127) *q++ = (char)b;
      else {
        *q++ = '\\';
        *q++ = (char)('0' + b / 100);
        *q++ = (char)('0' + b / 10 % 10);
        *q++ = (char)('0' + b % 10);
      }
    }
  }
  return (cherry_string)c;
}

cherry_int cherry_str_compare(cherry_string a, cherry_string b) {
  size_t la = cherry_str_size(a), lb = cherry_str_size(b);
  int r = memcmp(cherry_str_data(a), cherry_str_data(b), la < lb ? la : lb);
  if (r == 0) r = (la > lb) - (la < lb);
  return CHERRY_INT_SMALL(r < 0 ? -1 : r > 0 ? 1 : 0);
}

/* 64-bit FNV-1a over the UTF-8 bytes (FStarC.Hash.of_string). */
uint64_t cherry_str_fnv1a(cherry_string s) {
  const unsigned char *p = (const unsigned char *)cherry_str_data(s);
  size_t n = cherry_str_size(s);
  uint64_t h = 0xcbf29ce484222325u;
  for (size_t i = 0; i < n; i++) {
    h ^= p[i];
    h *= 0x100000001b3u;
  }
  return h;
}

cherry_string cherry_string_of_int(cherry_int x) {
  if (cherry_is_scalar(x)) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%" PRIdPTR, cherry_int_val(x));
    return cherry_str_of_bytes(buf, (size_t)n);
  }
  view a;
  view_of(x, &a);
  uint32_t len = a.len;
  uint32_t *t = (uint32_t *)xmalloc(sizeof(uint32_t) * len);
  memcpy(t, a.d, sizeof(uint32_t) * len);
  /* Base 10^9 digits, least significant first. */
  uint32_t *chunks = (uint32_t *)xmalloc(sizeof(uint32_t) * (len * 2 + 1));
  uint32_t nc = 0;
  while (len > 0) {
    uint64_t k = 0;
    for (uint32_t j = len; j-- > 0;) {
      uint64_t cur = (k << 32) | t[j];
      t[j] = (uint32_t)(cur / 1000000000u);
      k = cur % 1000000000u;
    }
    chunks[nc++] = (uint32_t)k;
    while (len > 0 && t[len - 1] == 0) len--;
  }
  char *buf = (char *)xmalloc((size_t)nc * 9 + 2);
  size_t n = 0;
  if (a.neg) buf[n++] = '-';
  n += (size_t)sprintf(buf + n, "%" PRIu32, chunks[nc - 1]);
  for (uint32_t i = nc - 1; i-- > 0;)
    n += (size_t)sprintf(buf + n, "%09" PRIu32, chunks[i]);
  cherry_string r = cherry_str_of_bytes(buf, n);
  free(buf);
  free(chunks);
  free(t);
  return r;
}

cherry_string cherry_string_of_bool(bool b) {
  return b ? cherry_str_of_bytes("true", 4) : cherry_str_of_bytes("false", 5);
}

void cherry_print_string(cherry_string s) {
  fwrite(cherry_str_data(s), 1, cherry_str_size(s), stdout);
}

/* ------------------------------------------------------------------------
   Realizations of ulib functions that OCaml realizes by hand and that have no
   F* definition to compile (doc/ref/cherry.md, "Library realizations").  The
   names are the ones Custard gives the externals; weak, so that a program may
   supply its own. */

#define CHERRY_WEAK __attribute__((weak))

uint64_t cherry_int_to_u64(cherry_int x) {
  if (cherry_is_scalar(x)) return (uint64_t)(int64_t)cherry_int_val(x);
  view a;
  view_of(x, &a);
  uint64_t r = 0;
  for (uint32_t i = 0; i < a.len && i < 2; i++) r |= (uint64_t)a.d[i] << (32 * i);
  return a.neg ? (uint64_t)0 - r : r;
}

int64_t cherry_int_to_i64(cherry_int x) { return (int64_t)cherry_int_to_u64(x); }

static cherry_int of_mag64(bool neg, uint64_t m) {
  uint32_t d[2] = { (uint32_t)m, (uint32_t)(m >> 32) };
  return big_from(neg, d, d[1] != 0 ? 2 : 1);
}

cherry_int cherry_int_of_i64(int64_t v) {
  if (cherry_int_fits((intptr_t)v) && (int64_t)(intptr_t)v == v)
    return CHERRY_INT_SMALL((intptr_t)v);
  return of_mag64(v < 0, v < 0 ? (uint64_t)0 - (uint64_t)v : (uint64_t)v);
}

cherry_int cherry_int_of_u64(uint64_t v) {
  if (v <= (uint64_t)CHERRY_INT_MAX) return CHERRY_INT_SMALL((intptr_t)v);
  return of_mag64(false, v);
}

#ifdef __SIZEOF_INT128__
cherry_u128 cherry_int_to_u128(cherry_int x) {
  if (cherry_is_scalar(x)) return (cherry_u128)(cherry_i128)cherry_int_val(x);
  view a;
  view_of(x, &a);
  cherry_u128 r = 0;
  for (uint32_t i = 0; i < a.len && i < 4; i++) r |= (cherry_u128)a.d[i] << (32 * i);
  return a.neg ? (cherry_u128)0 - r : r;
}

cherry_i128 cherry_int_to_i128(cherry_int x) { return (cherry_i128)cherry_int_to_u128(x); }

static cherry_int of_mag128(bool neg, cherry_u128 m) {
  uint32_t d[4], len = 0;
  for (; m != 0; m >>= 32) d[len++] = (uint32_t)m;
  return big_from(neg, d, len);
}

cherry_int cherry_int_of_u128(cherry_u128 v) {
  if (v <= (cherry_u128)CHERRY_INT_MAX) return CHERRY_INT_SMALL((intptr_t)v);
  return of_mag128(false, v);
}

cherry_int cherry_int_of_i128(cherry_i128 v) {
  if (v >= -(cherry_i128)CHERRY_INT_MAX && v <= (cherry_i128)CHERRY_INT_MAX)
    return CHERRY_INT_SMALL((intptr_t)v);
  return v < 0 ? of_mag128(true, (cherry_u128)0 - (cherry_u128)v)
               : of_mag128(false, (cherry_u128)v);
}
#endif

#define CHERRY_MACHINE_INT(M, T, FMT, OF)                                   \
  CHERRY_WEAK cherry_int FStar_##M##_v(T x) { return OF(x); }                \
  CHERRY_WEAK cherry_string FStar_##M##_to_string(T x) {                     \
    char buf[32];                                                            \
    int n = snprintf(buf, sizeof buf, "%" FMT, x);                           \
    return cherry_str_of_bytes(buf, (size_t)n);                              \
  }

CHERRY_MACHINE_INT(Int8, int8_t, PRId8, cherry_int_of_i64)
CHERRY_MACHINE_INT(Int16, int16_t, PRId16, cherry_int_of_i64)
CHERRY_MACHINE_INT(Int32, int32_t, PRId32, cherry_int_of_i64)
CHERRY_MACHINE_INT(Int64, int64_t, PRId64, cherry_int_of_i64)
CHERRY_MACHINE_INT(UInt8, uint8_t, PRIu8, cherry_int_of_u64)
CHERRY_MACHINE_INT(UInt16, uint16_t, PRIu16, cherry_int_of_u64)
CHERRY_MACHINE_INT(UInt32, uint32_t, PRIu32, cherry_int_of_u64)
CHERRY_MACHINE_INT(UInt64, uint64_t, PRIu64, cherry_int_of_u64)

#ifdef __SIZEOF_INT128__
/* printf has no 128-bit format: [to_string] goes through [Prims.int]. */
#define CHERRY_MACHINE_INT128(M, T, OF)                                      \
  CHERRY_WEAK cherry_int FStar_##M##_v(T x) { return OF(x); }                \
  CHERRY_WEAK cherry_string FStar_##M##_to_string(T x) {                     \
    cherry_int i = OF(x);                                                    \
    cherry_string s = cherry_string_of_int(i);                               \
    cherry_dec(i);                                                           \
    return s;                                                                \
  }
CHERRY_MACHINE_INT128(Int128, cherry_i128, cherry_int_of_i128)
CHERRY_MACHINE_INT128(UInt128, cherry_u128, cherry_int_of_u128)
#endif

CHERRY_WEAK void FStar_IO_print_newline(void) {
  putchar('\n');
  fflush(stdout);
}

/* [option int] and [option bool], laid out as Custard lays out a monomorphic
   [option]: the tag ([None] first) and then the payload. */
typedef struct { int tag; union { cherry_int v; } val; } cherry_option_int;
typedef struct { int tag; union { bool v; } val; } cherry_option_bool;

CHERRY_WEAK cherry_option_bool FStar_Parse_bool_of_string(cherry_string s) {
  cherry_option_bool r = { 0 };
  size_t n = cherry_str_size(s);
  const char *p = cherry_str_data(s);
  if (n == 4 && memcmp(p, "true", 4) == 0) { r.tag = 1; r.val.v = true; }
  else if (n == 5 && memcmp(p, "false", 5) == 0) { r.tag = 1; r.val.v = false; }
  return r;
}

/* As Zarith's [Z.of_string]: an optional sign, an optional 0x/0o/0b prefix,
   and at least one digit. */
CHERRY_WEAK cherry_option_int FStar_Parse_int_of_string(cherry_string s) {
  cherry_option_int r = { 0 };
  size_t n = cherry_str_size(s), i = 0;
  const char *p = cherry_str_data(s);
  bool neg = false;
  if (i < n && (p[i] == '-' || p[i] == '+')) neg = p[i++] == '-';
  int base = 10;
  if (i + 1 < n && p[i] == '0') {
    char c = p[i + 1];
    if (c == 'x' || c == 'X') base = 16;
    else if (c == 'o' || c == 'O') base = 8;
    else if (c == 'b' || c == 'B') base = 2;
    if (base != 10) i += 2;
  }
  if (i == n) return r;
  cherry_int acc = CHERRY_INT_SMALL(0), b = CHERRY_INT_SMALL(base);
  for (; i < n; i++) {
    char c = p[i];
    int d = c >= '0' && c <= '9' ? c - '0'
          : c >= 'a' && c <= 'f' ? c - 'a' + 10
          : c >= 'A' && c <= 'F' ? c - 'A' + 10 : 99;
    if (d >= base) { cherry_dec(acc); return r; }
    cherry_int m = cherry_int_mul(acc, b);
    cherry_dec(acc);
    acc = cherry_int_add(m, CHERRY_INT_SMALL(d));
    cherry_dec(m);
  }
  if (neg) { cherry_int t = cherry_int_neg(acc); cherry_dec(acc); acc = t; }
  r.tag = 1;
  r.val.v = acc;
  return r;
}

/* ------------------------------------------------------------------------
   Clock (FStarC.Timing). */

uint64_t cherry_now_ns(void) {
  struct timespec ts;
#ifdef CLOCK_MONOTONIC
  clock_gettime(CLOCK_MONOTONIC, &ts);
#else
  timespec_get(&ts, TIME_UTC);
#endif
  return (uint64_t)ts.tv_sec * 1000000000u + (uint64_t)ts.tv_nsec;
}

uint64_t cherry_wall_ns(void) {
  struct timespec ts;
  timespec_get(&ts, TIME_UTC);
  return (uint64_t)ts.tv_sec * 1000000000u + (uint64_t)ts.tv_nsec;
}

uint64_t cherry_file_mtime_ns(cherry_string path) {
  struct stat st;
  if (stat(cherry_str_data(path), &st) != 0) return UINT64_MAX;
  return (uint64_t)st.st_mtime * 1000000000u;
}

/* ------------------------------------------------------------------------
   The operating system, for FStarC.Util-c.cherry.fst: the command line,
   channels, files and directories, processes and signals.  An external
   cannot raise, so one that fails records a message instead, which the F*
   side takes with [cherry_io_error] and raises as [Failure]. */

static int cherry_argc_;
static char **cherry_argv_;

void cherry_set_args(int argc, char **argv) { cherry_argc_ = argc; cherry_argv_ = argv; }

cherry_int cherry_argc(void) { return cherry_int_of_i64(cherry_argc_); }

static cherry_string str_of_c(const char *p) { return cherry_str_of_bytes(p, strlen(p)); }

cherry_string cherry_argv(cherry_int i) {
  int64_t k = cherry_int_to_i64(i);
  return str_of_c(k >= 0 && k < cherry_argc_ ? cherry_argv_[k] : "");
}

static _Thread_local char *io_err;

/* [what: strerror(errno)] */
static void io_fail(const char *what) {
  const char *e = strerror(errno);
  size_t n = strlen(what) + strlen(e) + 3;
  free(io_err);
  io_err = (char *)malloc(n);
  if (io_err == NULL) abort();
  snprintf(io_err, n, "%s: %s", what, e);
}

static void io_fail_msg(const char *msg) {
  free(io_err);
  io_err = (char *)malloc(strlen(msg) + 1);
  if (io_err == NULL) abort();
  strcpy(io_err, msg);
}

cherry_string cherry_io_error(void) {
  if (io_err == NULL) return str_of_c("");
  cherry_string r = str_of_c(io_err);
  free(io_err);
  io_err = NULL;
  return r;
}

/* Channels are indices into a table of [FILE *]s; 0, 1 and 2 are stdin,
   stdout and stderr.  [eof] says whether the last line read hit the end. */
typedef struct { FILE *f; bool eof; } chan;
static chan *chans;
static size_t nchans, chans_cap;

static void chans_init(void) {
  if (chans != NULL) return;
  chans_cap = 16;
  chans = (chan *)calloc(chans_cap, sizeof(chan));
  if (chans == NULL) abort();
  chans[0].f = stdin; chans[1].f = stdout; chans[2].f = stderr;
  nchans = 3;
}

static uint64_t chan_add(FILE *f) {
  chans_init();
  for (size_t i = 3; i < nchans; i++)
    if (chans[i].f == NULL) { chans[i].f = f; chans[i].eof = false; return i; }
  if (nchans == chans_cap) {
    chans_cap *= 2;
    chans = (chan *)realloc(chans, chans_cap * sizeof(chan));
    if (chans == NULL) abort();
  }
  chans[nchans].f = f; chans[nchans].eof = false;
  return nchans++;
}

static FILE *chan_get(uint64_t h) {
  chans_init();
  return h < nchans ? chans[h].f : NULL;
}

static FILE *chan_get_or_fail(uint64_t h) {
  FILE *f = chan_get(h);
  if (f == NULL) io_fail_msg("Bad file descriptor (channel closed)");
  return f;
}

uint64_t cherry_chan_open(cherry_string path, uint32_t mode) {
  static const char *const modes[] = { "rb", "wb", "ab" };
  FILE *f = fopen(cherry_str_data(path), modes[mode < 3 ? mode : 0]);
  if (f == NULL) { io_fail(cherry_str_data(path)); return UINT64_MAX; }
  return chan_add(f);
}

void cherry_chan_close(uint64_t h) {
  FILE *f = chan_get(h);
  if (f == NULL) return;
  if (h < 3) { fflush(f); return; }
  chans[h].f = NULL;
  if (fclose(f) != 0) io_fail("close");
}

/* Closes the descriptor without flushing first, as killing a process does
   with its pipes: the buffered data is lost. */
void cherry_chan_close_fd(uint64_t h) {
  FILE *f = chan_get(h);
  if (f == NULL || h < 3) return;
  chans[h].f = NULL;
  close(fileno(f));
  fclose(f);
}

void cherry_chan_flush(uint64_t h) {
  FILE *f = chan_get_or_fail(h);
  if (f != NULL && fflush(f) != 0) io_fail("flush");
}

void cherry_chan_output(uint64_t h, cherry_string s) {
  FILE *f = chan_get_or_fail(h);
  if (f == NULL) return;
  size_t n = cherry_str_size(s);
  if (n != 0 && fwrite(cherry_str_data(s), 1, n, f) != n) io_fail("output");
}

/* A line without its newline; at the end of input, "" and [eof] set. */
cherry_string cherry_chan_input_line(uint64_t h) {
  FILE *f = chan_get_or_fail(h);
  if (f == NULL) return str_of_c("");
  char *line = NULL;
  size_t cap = 0;
  ssize_t n = getline(&line, &cap, f);
  chans[h].eof = n < 0;
  if (n < 0) { free(line); return str_of_c(""); }
  if (n > 0 && line[n - 1] == '\n') n--;
  cherry_string r = cherry_str_of_bytes(line, (size_t)n);
  free(line);
  return r;
}

bool cherry_chan_eof(uint64_t h) { chans_init(); return h < nchans && chans[h].eof; }

/* Up to [max] bytes, all of them if [max] is UINT64_MAX; [eof] is set when
   there were none. */
cherry_string cherry_chan_read(uint64_t h, uint64_t max) {
  FILE *f = chan_get_or_fail(h);
  if (f == NULL) return str_of_c("");
  size_t len = 0, cap = 4096;
  char *buf = (char *)malloc(cap);
  if (buf == NULL) abort();
  while (len < max) {
    if (len == cap) {
      cap *= 2;
      buf = (char *)realloc(buf, cap);
      if (buf == NULL) abort();
    }
    size_t want = cap - len;
    if (max - len < want) want = (size_t)(max - len);
    size_t got = fread(buf + len, 1, want, f);
    len += got;
    if (got < want) break;
  }
  chans[h].eof = len == 0 && max != 0;
  cherry_string r = cherry_str_of_bytes(buf, len);
  free(buf);
  return r;
}

/* What can be read from [h]'s descriptor without blocking, up to [max]. */
cherry_string cherry_chan_read_nonblock(uint64_t h, uint64_t max) {
  FILE *f = chan_get(h);
  if (f == NULL) return str_of_c("");
  int fd = fileno(f);
  size_t len = 0, cap = max < 4096 ? (size_t)max : 4096;
  char *buf = (char *)malloc(cap + 1);
  if (buf == NULL) abort();
  while (len < cap) {
    struct pollfd p = { fd, POLLIN, 0 };
    if (poll(&p, 1, 0) <= 0 || !(p.revents & (POLLIN | POLLHUP))) break;
    ssize_t n = read(fd, buf + len, cap - len);
    if (n <= 0) break;
    len += (size_t)n;
  }
  cherry_string r = cherry_str_of_bytes(buf, len);
  free(buf);
  return r;
}

bool cherry_poll_stdin(double secs) {
  struct pollfd p = { 0, POLLIN, 0 };
  return poll(&p, 1, (int)(secs * 1000.0)) > 0;
}

/* 0 if [path] was created, 1 if it exists already, 2 if its parent does
   not, 3 (with the error recorded) otherwise. */
cherry_int cherry_mkdir(cherry_string path) {
  if (mkdir(cherry_str_data(path), 0777) == 0) return CHERRY_INT_SMALL(0);
  if (errno == EEXIST) return CHERRY_INT_SMALL(1);
  if (errno == ENOENT) return CHERRY_INT_SMALL(2);
  io_fail(cherry_str_data(path));
  return CHERRY_INT_SMALL(3);
}

void cherry_set_umask(void) { umask(002); }

void cherry_remove_all_in_dir(cherry_string path) {
  const char *d = cherry_str_data(path);
  DIR *dir = opendir(d);
  if (dir == NULL) { io_fail(d); return; }
  struct dirent *e;
  while ((e = readdir(dir)) != NULL) {
    if (strcmp(e->d_name, ".") == 0 || strcmp(e->d_name, "..") == 0) continue;
    size_t n = strlen(d) + strlen(e->d_name) + 2;
    char *p = (char *)malloc(n);
    if (p == NULL) abort();
    snprintf(p, n, "%s/%s", d, e->d_name);
    if (remove(p) != 0) { io_fail(p); free(p); break; }
    free(p);
  }
  closedir(dir);
}

bool cherry_file_exists(cherry_string path) {
  struct stat st;
  return stat(cherry_str_data(path), &st) == 0;
}

bool cherry_is_directory(cherry_string path) {
  struct stat st;
  return stat(cherry_str_data(path), &st) == 0 && S_ISDIR(st.st_mode);
}

/* As OCaml's Filename.dirname and Filename.basename on Unix: trailing
   slashes are not a component, and "" is ".". */
cherry_string cherry_dirname(cherry_string path) {
  const char *p = cherry_str_data(path);
  size_t n = cherry_str_size(path);
  while (n > 0 && p[n - 1] == '/') n--;
  if (n == 0) return str_of_c(cherry_str_size(path) == 0 ? "." : "/");
  while (n > 0 && p[n - 1] != '/') n--;
  if (n == 0) return str_of_c(".");
  while (n > 0 && p[n - 1] == '/') n--;
  if (n == 0) return str_of_c("/");
  return cherry_str_of_bytes(p, n);
}

cherry_string cherry_basename(cherry_string path) {
  const char *p = cherry_str_data(path);
  size_t n = cherry_str_size(path);
  while (n > 0 && p[n - 1] == '/') n--;
  if (n == 0) return str_of_c(cherry_str_size(path) == 0 ? "." : "/");
  size_t i = n;
  while (i > 0 && p[i - 1] != '/') i--;
  return cherry_str_of_bytes(p + i, n - i);
}

void cherry_copy_file(cherry_string from, cherry_string to) {
  int in = open(cherry_str_data(from), O_RDONLY);
  if (in < 0) { io_fail(cherry_str_data(from)); return; }
  int out = open(cherry_str_data(to), O_WRONLY | O_CREAT | O_TRUNC, 0666);
  if (out < 0) { io_fail(cherry_str_data(to)); close(in); return; }
  char buf[8192];
  ssize_t n;
  while ((n = read(in, buf, sizeof buf)) > 0)
    if (write(out, buf, (size_t)n) != n) { io_fail(cherry_str_data(to)); break; }
  if (n < 0) io_fail(cherry_str_data(from));
  close(in);
  close(out);
}

void cherry_remove_file(cherry_string path) {
  if (remove(cherry_str_data(path)) != 0) io_fail(cherry_str_data(path));
}

void cherry_rename_file(cherry_string from, cherry_string to) {
  if (rename(cherry_str_data(from), cherry_str_data(to)) != 0) io_fail(cherry_str_data(from));
}

cherry_string cherry_file_get_contents(cherry_string path) {
  uint64_t h = cherry_chan_open(path, 0);
  if (h == UINT64_MAX) return str_of_c("");
  cherry_string r = cherry_chan_read(h, UINT64_MAX);
  cherry_chan_close(h);
  return r;
}

void cherry_touch_file(cherry_string path) {
  if (utimensat(AT_FDCWD, cherry_str_data(path), NULL, 0) != 0) io_fail(cherry_str_data(path));
}

cherry_string cherry_getcwd(void) {
  char *d = getcwd(NULL, 0);
  if (d == NULL) { io_fail("getcwd"); return str_of_c(""); }
  cherry_string r = str_of_c(d);
  free(d);
  return r;
}

/* The entries of a directory but "." and "..", in readdir's order (as
   OCaml's Sys.readdir), each followed by a NUL byte. */
cherry_string cherry_readdir(cherry_string path) {
  DIR *dir = opendir(cherry_str_data(path));
  if (dir == NULL) { io_fail(cherry_str_data(path)); return str_of_c(""); }
  char *buf = NULL;
  size_t n = 0, cap = 0;
  struct dirent *e;
  while ((e = readdir(dir)) != NULL) {
    if (strcmp(e->d_name, ".") == 0 || strcmp(e->d_name, "..") == 0) continue;
    size_t k = strlen(e->d_name) + 1;
    if (n + k > cap) {
      cap = 2 * (n + k);
      buf = (char *)realloc(buf, cap);
      if (buf == NULL) abort();
    }
    memcpy(buf + n, e->d_name, k);
    n += k;
  }
  closedir(dir);
  /* Without the last NUL, so that splitting at NULs gives the entries. */
  cherry_string r = cherry_str_of_bytes(buf != NULL ? buf : "", n == 0 ? 0 : n - 1);
  free(buf);
  return r;
}

/* Whether two paths name the same file (device and inode). */
bool cherry_same_file(cherry_string a, cherry_string b) {
  struct stat sa, sb;
  if (stat(cherry_str_data(a), &sa) != 0) { io_fail(cherry_str_data(a)); return false; }
  if (stat(cherry_str_data(b), &sb) != 0) { io_fail(cherry_str_data(b)); return false; }
  return sa.st_dev == sb.st_dev && sa.st_ino == sb.st_ino;
}

bool cherry_isatty(uint64_t h) {
  FILE *f = chan_get(h);
  return f != NULL && isatty(fileno(f));
}

/* What the uname command prints: the kernel's name. */
cherry_string cherry_uname(void) {
  struct utsname u;
  return str_of_c(uname(&u) == 0 ? u.sysname : "Unix");
}

/* The executable's resolved path; argv[0] where it cannot be found. */
cherry_string cherry_exec_name(void) {
  char buf[PATH_MAX];
  const char *p = cherry_argc_ > 0 ? cherry_argv_[0] : "";
#if defined(__APPLE__)
  uint32_t size = sizeof buf;
  if (_NSGetExecutablePath(buf, &size) == 0) p = buf;
#else
  ssize_t n = readlink("/proc/self/exe", buf, sizeof buf - 1);
  if (n > 0) { buf[n] = 0; p = buf; }
#endif
  char *r = realpath(p, NULL);
  cherry_string s = str_of_c(r != NULL ? r : p);
  free(r);
  return s;
}

bool cherry_has_env(cherry_string name) { return getenv(cherry_str_data(name)) != NULL; }

cherry_string cherry_getenv(cherry_string name) {
  const char *v = getenv(cherry_str_data(name));
  return str_of_c(v != NULL ? v : "");
}

void cherry_setenv(cherry_string name, cherry_string value) {
  if (setenv(cherry_str_data(name), cherry_str_data(value), 1) != 0) io_fail("putenv");
}

/* Processes.  The arguments are pushed one by one ([cherry_proc_arg]) and
   used by the next spawn, which also takes them. */
static char **pargs;
static size_t npargs, pargs_cap;

void cherry_proc_arg(cherry_string a) {
  if (npargs + 1 >= pargs_cap) {
    pargs_cap = pargs_cap == 0 ? 16 : 2 * pargs_cap;
    pargs = (char **)realloc(pargs, pargs_cap * sizeof(char *));
    if (pargs == NULL) abort();
  }
  size_t n = cherry_str_size(a);
  char *c = (char *)malloc(n + 1);
  if (c == NULL) abort();
  memcpy(c, cherry_str_data(a), n + 1);
  pargs[npargs++] = c;
  pargs[npargs] = NULL;
}

static void pargs_clear(void) {
  for (size_t i = 0; i < npargs; i++) free(pargs[i]);
  npargs = 0;
  if (pargs != NULL) pargs[0] = NULL;
}

static uint64_t spawned[3];

extern char **environ;

/* Runs [prog] (searched in the PATH) with the pushed arguments as its argv.
   With [piped], its stdin, stdout and stderr are pipes, which
   [cherry_spawned_chan] then returns as channels (0: stdout, 1: stderr,
   2: stdin).  The pid, or -1 with the error recorded.  Writing to a child
   that has exited must fail rather than kill us, so a piped spawn ignores
   SIGPIPE from then on (as F*'s OCaml main blocks it); the child gets the
   default back. */
cherry_int cherry_spawn(cherry_string prog, bool piped) {
  if (pargs == NULL) {
    pargs_cap = 16;
    pargs = (char **)calloc(pargs_cap, sizeof(char *));
    if (pargs == NULL) abort();
  }
  int fds[3][2] = { { -1, -1 }, { -1, -1 }, { -1, -1 } };
  posix_spawn_file_actions_t fa;
  posix_spawn_file_actions_init(&fa);
  if (piped) {
    for (int i = 0; i < 3; i++) {
      if (pipe(fds[i]) != 0) {
        io_fail("pipe");
        for (int j = 0; j < i; j++) { close(fds[j][0]); close(fds[j][1]); }
        posix_spawn_file_actions_destroy(&fa);
        pargs_clear();
        return CHERRY_INT_SMALL(-1);
      }
      fcntl(fds[i][0], F_SETFD, FD_CLOEXEC);
      fcntl(fds[i][1], F_SETFD, FD_CLOEXEC);
    }
    posix_spawn_file_actions_adddup2(&fa, fds[0][0], 0);
    posix_spawn_file_actions_adddup2(&fa, fds[1][1], 1);
    posix_spawn_file_actions_adddup2(&fa, fds[2][1], 2);
  }
  posix_spawnattr_t at;
  posix_spawnattr_init(&at);
  if (piped) {
    signal(SIGPIPE, SIG_IGN);
    sigset_t def;
    sigemptyset(&def);
    sigaddset(&def, SIGPIPE);
    posix_spawnattr_setsigdefault(&at, &def);
    posix_spawnattr_setflags(&at, POSIX_SPAWN_SETSIGDEF);
  }
  fflush(NULL);
  pid_t pid;
  int rc = posix_spawnp(&pid, cherry_str_data(prog), &fa, &at, pargs, environ);
  posix_spawn_file_actions_destroy(&fa);
  posix_spawnattr_destroy(&at);
  pargs_clear();
  if (piped) {
    close(fds[0][0]);
    close(fds[1][1]);
    close(fds[2][1]);
    if (rc != 0) { close(fds[0][1]); close(fds[1][0]); close(fds[2][0]); }
  }
  if (rc != 0) { errno = rc; io_fail(cherry_str_data(prog)); return CHERRY_INT_SMALL(-1); }
  if (piped) {
    spawned[0] = chan_add(fdopen(fds[1][0], "rb"));
    spawned[1] = chan_add(fdopen(fds[2][0], "rb"));
    spawned[2] = chan_add(fdopen(fds[0][1], "wb"));
  }
  return cherry_int_of_i64(pid);
}

uint64_t cherry_spawned_chan(uint32_t i) { return spawned[i < 3 ? i : 0]; }

/* The process may be gone already. */
void cherry_kill(cherry_int pid) { kill((pid_t)cherry_int_to_i64(pid), SIGKILL); }

/* The exit status, or 256 + the signal that killed it; -1 with the error
   recorded. */
cherry_int cherry_waitpid(cherry_int pid) {
  int st;
  for (;;) {
    if (waitpid((pid_t)cherry_int_to_i64(pid), &st, 0) >= 0) break;
    if (errno != EINTR) { io_fail("waitpid"); return CHERRY_INT_SMALL(-1); }
  }
  if (WIFEXITED(st)) return CHERRY_INT_SMALL(WEXITSTATUS(st));
  if (WIFSIGNALED(st)) return CHERRY_INT_SMALL(256 + WTERMSIG(st));
  return CHERRY_INT_SMALL(255);
}

/* As OCaml's Sys.command: the exit status, or 255. */
cherry_int cherry_system(cherry_string cmd) {
  fflush(NULL);
  int st = system(cherry_str_data(cmd));
  if (st != -1 && WIFEXITED(st)) return CHERRY_INT_SMALL(WEXITSTATUS(st));
  return CHERRY_INT_SMALL(255);
}

/* 0: default, 1: ignore. */
void cherry_set_sigint(uint32_t mode) { signal(SIGINT, mode == 1 ? SIG_IGN : SIG_DFL); }

void cherry_sleep_ms(cherry_int n) {
  int64_t ms = cherry_int_to_i64(n);
  if (ms <= 0) return;
  struct timespec ts = { (time_t)(ms / 1000), (long)(ms % 1000) * 1000000L };
  while (nanosleep(&ts, &ts) != 0 && errno == EINTR) {}
}

/* Processor time in seconds, as OCaml's Sys.time. */
double cherry_cpu_time(void) { return (double)clock() / CLOCKS_PER_SEC; }

/* As OCaml's string_of_float: "%.12g", with a "." if it reads as an integer. */
cherry_string cherry_string_of_float(double d) {
  char buf[64];
  if (d != d) return str_of_c("nan");
  if (d == 1.0 / 0.0) return str_of_c("inf");
  if (d == -1.0 / 0.0) return str_of_c("-inf");
  snprintf(buf, sizeof buf - 1, "%.12g", d);
  if (strspn(buf, "-0123456789") == strlen(buf)) strcat(buf, ".");
  return str_of_c(buf);
}

/* strtod, after dropping the underscores OCaml allows; [ok] says whether the
   whole string was a number. */
static double parse_float(cherry_string s, bool *ok) {
  size_t n = cherry_str_size(s);
  const char *p = cherry_str_data(s);
  char *c = (char *)malloc(n + 1), *end;
  if (c == NULL) abort();
  size_t k = 0;
  for (size_t i = 0; i < n; i++) if (p[i] != '_') c[k++] = p[i];
  c[k] = 0;
  double d = strtod(c, &end);
  *ok = k > 0 && *end == 0 && strlen(c) == k;
  free(c);
  return d;
}

bool cherry_float_of_string_ok(cherry_string s) { bool ok; parse_float(s, &ok); return ok; }

double cherry_float_of_string(cherry_string s) { bool ok; return parse_float(s, &ok); }

double cherry_f64_of_i64(int64_t i) { return (double)i; }

/* An exception as text: its F* name, and its message if it has one. */
cherry_string cherry_exn_to_string(cherry_exn e) {
  const cherry_exn_info *info = ((cherry_exn_hdr *)e)->info;
  if (info->msg == 0) return str_of_c(info->name);
  const char *m = cherry_str_data(*(cherry_string *)((char *)e + info->msg));
  size_t n = strlen(info->name) + strlen(m) + 5;
  char *b = (char *)malloc(n);
  if (b == NULL) abort();
  snprintf(b, n, "%s(\"%s\")", info->name, m);
  cherry_string r = str_of_c(b);
  free(b);
  return r;
}

/* Base64 without padding, as Batteries' BatBase64: decoding drops the bits
   left over at the end, and fails ([ok] false) on a character outside the
   alphabet, "=" included. */
static const char b64[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

cherry_string cherry_base64_encode(cherry_string s) {
  const unsigned char *p = (const unsigned char *)cherry_str_data(s);
  size_t n = cherry_str_size(s), k = 0;
  char *out = (char *)malloc(n / 3 * 4 + 5);
  if (out == NULL) abort();
  uint32_t acc = 0;
  int bits = 0;
  for (size_t i = 0; i < n; i++) {
    acc = (acc << 8) | p[i];
    bits += 8;
    while (bits >= 6) { bits -= 6; out[k++] = b64[(acc >> bits) & 63]; }
  }
  if (bits > 0) out[k++] = b64[(acc << (6 - bits)) & 63];
  cherry_string r = cherry_str_of_bytes(out, k);
  free(out);
  return r;
}

static cherry_string base64_decode(cherry_string s, bool *ok) {
  const char *p = cherry_str_data(s);
  size_t n = cherry_str_size(s), k = 0;
  char *out = (char *)malloc(n + 1);
  if (out == NULL) abort();
  uint32_t acc = 0;
  int bits = 0;
  *ok = true;
  for (size_t i = 0; i < n; i++) {
    const char *q = p[i] != 0 ? strchr(b64, p[i]) : NULL;
    if (q == NULL) { *ok = false; break; }
    acc = (acc << 6) | (uint32_t)(q - b64);
    bits += 6;
    if (bits >= 8) { bits -= 8; out[k++] = (char)((acc >> bits) & 0xFF); }
  }
  cherry_string r = cherry_str_of_bytes(out, *ok ? k : 0);
  free(out);
  return r;
}

bool cherry_base64_ok(cherry_string s) { bool ok; cherry_dec(base64_decode(s, &ok)); return ok; }

cherry_string cherry_base64_decode(cherry_string s) { bool ok; return base64_decode(s, &ok); }

/* MD5 (RFC 1321), for the digests of FStarC.Util, in lowercase hex. */
typedef struct { uint32_t h[4]; uint64_t len; unsigned char buf[64]; size_t n; } md5_ctx;

static const uint32_t md5_k[64] = {
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391,
};

static const unsigned char md5_r[16] = { 7, 12, 17, 22, 5, 9, 14, 20, 4, 11, 16, 23, 6, 10, 15, 21 };

static void md5_block(md5_ctx *c, const unsigned char *b) {
  uint32_t m[16];
  for (int i = 0; i < 16; i++)
    m[i] = (uint32_t)b[4 * i] | (uint32_t)b[4 * i + 1] << 8 |
           (uint32_t)b[4 * i + 2] << 16 | (uint32_t)b[4 * i + 3] << 24;
  uint32_t a = c->h[0], bb = c->h[1], cc = c->h[2], d = c->h[3];
  for (int i = 0; i < 64; i++) {
    uint32_t f;
    int g;
    switch (i / 16) {
      case 0: f = (bb & cc) | (~bb & d); g = i; break;
      case 1: f = (d & bb) | (~d & cc); g = (5 * i + 1) % 16; break;
      case 2: f = bb ^ cc ^ d; g = (3 * i + 5) % 16; break;
      default: f = cc ^ (bb | ~d); g = (7 * i) % 16; break;
    }
    f += a + md5_k[i] + m[g];
    int r = md5_r[(i / 16) * 4 + i % 4];
    a = d; d = cc; cc = bb;
    bb += (f << r) | (f >> (32 - r));
  }
  c->h[0] += a; c->h[1] += bb; c->h[2] += cc; c->h[3] += d;
}

static void md5_init(md5_ctx *c) {
  c->h[0] = 0x67452301; c->h[1] = 0xefcdab89; c->h[2] = 0x98badcfe; c->h[3] = 0x10325476;
  c->len = 0; c->n = 0;
}

static void md5_update(md5_ctx *c, const unsigned char *p, size_t n) {
  c->len += n;
  while (n > 0) {
    size_t k = 64 - c->n < n ? 64 - c->n : n;
    memcpy(c->buf + c->n, p, k);
    c->n += k; p += k; n -= k;
    if (c->n == 64) { md5_block(c, c->buf); c->n = 0; }
  }
}

static cherry_string md5_hex(md5_ctx *c) {
  uint64_t bits = c->len * 8;
  unsigned char pad[72] = { 0x80 };
  size_t padn = (c->n < 56 ? 56 : 120) - c->n;
  for (int i = 0; i < 8; i++) pad[padn + i] = (unsigned char)(bits >> (8 * i));
  md5_update(c, pad, padn + 8);
  char hex[33];
  for (int i = 0; i < 16; i++)
    snprintf(hex + 2 * i, 3, "%02x", (unsigned)(c->h[i / 4] >> (8 * (i % 4))) & 0xFF);
  return cherry_str_of_bytes(hex, 32);
}

cherry_string cherry_md5_hex(cherry_string s) {
  md5_ctx c;
  md5_init(&c);
  md5_update(&c, (const unsigned char *)cherry_str_data(s), cherry_str_size(s));
  return md5_hex(&c);
}

cherry_string cherry_md5_hex_file(cherry_string path) {
  FILE *f = fopen(cherry_str_data(path), "rb");
  if (f == NULL) { io_fail(cherry_str_data(path)); return str_of_c(""); }
  md5_ctx c;
  md5_init(&c);
  unsigned char buf[8192];
  size_t n;
  while ((n = fread(buf, 1, sizeof buf, f)) > 0) md5_update(&c, buf, n);
  fclose(f);
  return md5_hex(&c);
}
