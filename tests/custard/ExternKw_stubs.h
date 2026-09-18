#ifndef EXTERN_KW_STUBS_H
#define EXTERN_KW_STUBS_H 1

/* A macro whose argument is a *type*, which is why the token passed to it has
   to survive verbatim: [KW_SIZEOF(float_)] names nothing. */
#define KW_SIZEOF(ty) ((uint64_t)sizeof(ty))

#endif
