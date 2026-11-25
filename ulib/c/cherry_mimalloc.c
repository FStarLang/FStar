/* mimalloc, linked statically: compiling this file into a Cherry program
   replaces malloc, free and realloc everywhere in the process (the runtime,
   the generated code and libc alike) with mimalloc's (cherry.md, Allocation).
   It needs -I$(CHERRY_INC)/mimalloc/include; leaving it out of the link keeps
   the system allocator.

   mimalloc is release-built, whether or not NDEBUG is set, unless the build
   defines MI_DEBUG.  Under AddressSanitizer, which brings its own allocator,
   this file is empty. */

#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#define CHERRY_MIMALLOC_ASAN
#endif
#endif
#if defined(__SANITIZE_ADDRESS__)
#define CHERRY_MIMALLOC_ASAN
#endif

#ifndef CHERRY_MIMALLOC_ASAN
#if !defined(MI_DEBUG) && !defined(MI_BUILD_RELEASE)
#define MI_BUILD_RELEASE
#endif
#ifndef MI_MALLOC_OVERRIDE
#define MI_MALLOC_OVERRIDE 1
#endif
#include "mimalloc/src/static.c"
#else
typedef int cherry_mimalloc_unused; /* ISO C forbids an empty unit */
#endif
