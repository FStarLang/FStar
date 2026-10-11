/* Slow paths of the Cherry runtime: deferred work, big integers and strings.  See cherry.h.

   Big integers are sign and magnitude, the magnitude in 32-bit limbs, least
   significant first, with no leading zero limbs.  A result that fits in a
   small integer is always returned as one. */
#include "cherry.h"

#include <inttypes.h>
#include <stdio.h>

/* ------------------------------------------------------------------------
   Deferred work (cherry.h): one work list per thread, kept between walks. */

typedef struct { cherry_obj *o; cherry_work_fn f; int mode; } job;

static _Thread_local job *jobs;
static _Thread_local size_t njobs, cap;
static _Thread_local bool busy;

_Thread_local cherry_exn cherry_exn_slot;

void cherry_exn_uncaught(void) {
  cherry_exn e = cherry_exn_take();
  fflush(stdout);
  fprintf(stderr, "Uncaught exception: %s\n", ((cherry_exn_hdr *)e)->info->name);
  cherry_exn_dec(e);
  exit(2);
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
  cherry_int q;
  big_edivmod(a, b, &q, NULL);
  return q;
}

cherry_int cherry_big_erem(cherry_int a, cherry_int b) {
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
  size_t n = x->size + y->size;
  if (x->hdr.rc == 1) {
    /* Functional but in place: nobody else can see [a]. */
    if (n + 1 > x->cap) {
      size_t cap = 2 * n + 1;
      x = (cherry_string_cell *)realloc(x, sizeof(cherry_string_cell) + cap);
      if (x == NULL) abort();
      x->cap = cap;
    }
    memmove(x->data + x->size, y->data, y->size);
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

cherry_int cherry_str_compare(cherry_string a, cherry_string b) {
  size_t la = cherry_str_size(a), lb = cherry_str_size(b);
  int r = memcmp(cherry_str_data(a), cherry_str_data(b), la < lb ? la : lb);
  if (r == 0) r = (la > lb) - (la < lb);
  return CHERRY_INT_SMALL(r < 0 ? -1 : r > 0 ? 1 : 0);
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

void cherry_print_string(cherry_string s) {
  fwrite(cherry_str_data(s), 1, cherry_str_size(s), stdout);
}
