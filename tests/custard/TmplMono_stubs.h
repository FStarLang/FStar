/* The target side of TmplMono.fst: a C++ class template standing in for
   wmma::fragment<...>, whose non-type parameter is the size index Custard
   has to have as a constant.  The point of the file is that `16' arrives in
   the *type*, which is what makes a monomorphized value argument safe here
   (section 85.3) -- the realization does learn what it was. */

#ifndef __TMPLMONO_STUBS_H
#define __TMPLMONO_STUBS_H

#include <stddef.h>

namespace wm {

template <size_t N> struct frag { size_t v; };

/* Deduced from the argument, which is why the F* side needs no template-id
   for it. */
template <size_t N> static inline void fill(frag<N> f, size_t v) {
  (void) f; (void) v;
}

static inline frag<16> mk16(size_t seed) { frag<16> f; f.v = seed; return f; }

/* The section 92 shapes: a [nat]-indexed template, and a factory with a
   template-id of its own since C++ deduces nothing from a return type. */
template <size_t N> struct nfrag { size_t v; };

static inline nfrag<16> nmk16(size_t seed) { nfrag<16> f; f.v = seed; return f; }

template <size_t N> static inline void nfill(nfrag<N> f, size_t v) {
  (void) f; (void) v;
}

}

#endif
