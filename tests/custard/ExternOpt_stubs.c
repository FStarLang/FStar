/* The realizations of [listen] and [close], written against the struct
   Custard generated for [option listener].

   Section 72's warning 377 says out loud that the name is a specialization
   hint, and advises a consumer that must spell it to typedef it once -- which
   is what this file does, so that the rest of it reads as the author meant. */

#include "ExternOpt.h"

typedef FStar_Pervasives_Native_option__listener opt_listener;

opt_listener ExternOpt_listen(uint32_t n) {
  opt_listener r;
  if (n == (uint32_t)0) {
    r.tag = FSTAR_PERVASIVES_NATIVE_NONE__LISTENER;
    return r;
  }
  r.tag = FSTAR_PERVASIVES_NATIVE_SOME__LISTENER;
  r.val.FStar_Pervasives_Native_Some__listener.v.port = n;
  return r;
}

uint32_t ExternOpt_close(opt_listener o) {
  if (o.tag == FSTAR_PERVASIVES_NATIVE_NONE__LISTENER) return (uint32_t)0;
  return o.val.FStar_Pervasives_Native_Some__listener.v.port;
}
