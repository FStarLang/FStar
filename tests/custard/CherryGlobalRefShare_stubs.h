#ifndef __CHERRYGLOBALREFSHARE_STUBS_H
#define __CHERRYGLOBALREFSHARE_STUBS_H
#include "cherry.h"
static inline bool ext_is_shared(void *l) {
  cherry_obj *o = (cherry_obj *)l;
  return !cherry_is_scalar(o) && cherry_rc_load(o) < 0;
}
static inline void ext_start_threads(void) { cherry_start_threads(); }
#endif
