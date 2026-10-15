#ifndef __CHERRYEXTOWN_STUBS_H
#define __CHERRYEXTOWN_STUBS_H
#include "cherry.h"
static inline uint32_t ext_len_borrowed(cherry_string s) {
  return (uint32_t)cherry_str_size(s);
}
static inline uint32_t ext_len_owned(cherry_string s, uint32_t k) {
  uint32_t n = (uint32_t)cherry_str_size(s) + k;
  cherry_dec(s);
  return n;
}
#endif
