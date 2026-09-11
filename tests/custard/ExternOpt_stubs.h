/* The target's half of ExternOpt.fst: the type Custard is told nothing about
   beyond its C name.  [option listener] is *not* here -- that one Custard
   generates, and ExternOpt_stubs.c is written against the generated header. */

#ifndef __EXTERNOPT_STUBS_H
#define __EXTERNOPT_STUBS_H

#include <stdint.h>

typedef struct {
  uint32_t port;
} externopt_listener_t;

static inline uint32_t externopt_port(externopt_listener_t l) { return l.port; }

#endif
