#include "Crypto_Symmetric_GF128_Spec.h"

void *Crypto_Symmetric_GF128_Spec_zero;

void *Crypto_Symmetric_GF128_Spec_encode(void *x)
{
  return x;
}

void *Crypto_Symmetric_GF128_Spec_poly(void *vs, void *r)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void *Crypto_Symmetric_GF128_Spec_finish(void *a, void *s)
{
  return Crypto_Symmetric_GF128_Spec_op_Plus_At(a, s);
}

void *Crypto_Symmetric_GF128_Spec_mac(void *vs, void *r, void *s)
{
  return Crypto_Symmetric_GF128_Spec_finish(Crypto_Symmetric_GF128_Spec_poly(vs, r), s);
}

