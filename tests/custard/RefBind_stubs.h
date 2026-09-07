#ifndef REF_BIND_STUBS_H
#define REF_BIND_STUBS_H 1

/* A C++ value object: copyable, so a copy of one compiles and silently
   discards every write made through it.  That is the whole difficulty --
   there is no diagnostic to switch on. */
typedef struct { uint32_t n; } rb_cell;

static rb_cell rb_slot;

static inline rb_cell rb_make(void) { rb_cell c; c.n = 0; return c; }
static inline void rb_bump(rb_cell &c) { c.n++; }
static inline uint32_t rb_get(rb_cell &c) { return c.n; }

#endif
