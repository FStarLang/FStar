#include "Crypto_Symmetric_Poly1305_Spec.h"

Prims_nat Crypto_Symmetric_Poly1305_Spec_p_1305;

uint32_t Crypto_Symmetric_Poly1305_Spec_taglen = (uint32_t )16;

void *Crypto_Symmetric_Poly1305_Spec_zero;

Prims_nat Crypto_Symmetric_Poly1305_Spec_field_add(Prims_nat a, Prims_nat b)
{
  return Prims_op_Modulus(Prims_op_Addition(a, b), Crypto_Symmetric_Poly1305_Spec_p_1305);
}

Prims_nat Crypto_Symmetric_Poly1305_Spec_field_mul(Prims_nat a, Prims_nat b)
{
  return Prims_op_Modulus(FStar_Mul_op_Star(a, b), Crypto_Symmetric_Poly1305_Spec_p_1305);
}

Prims_nat Crypto_Symmetric_Poly1305_Spec_op_Plus_At(Prims_nat x0, Prims_nat x1)
{
  return Crypto_Symmetric_Poly1305_Spec_field_add(x0, x1);
}

Prims_nat Crypto_Symmetric_Poly1305_Spec_op_Star_At(Prims_nat x0, Prims_nat x1)
{
  return Crypto_Symmetric_Poly1305_Spec_field_mul(x0, x1);
}

Prims_nat Crypto_Symmetric_Poly1305_Spec_encode(void *w)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_nat Crypto_Symmetric_Poly1305_Spec_trunc_1305(Prims_nat e)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_nat Crypto_Symmetric_Poly1305_Spec_poly(void *vs, Prims_nat r)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

bool Crypto_Symmetric_Poly1305_Spec_eq_poly0(void *p)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

bool Crypto_Symmetric_Poly1305_Spec_eq_poly(void *p0, void *p1)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_nat Crypto_Symmetric_Poly1305_Spec_clamp(void *r)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void *Crypto_Symmetric_Poly1305_Spec_finish(Prims_nat a, void *s)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void *Crypto_Symmetric_Poly1305_Spec_mac_1305(void *vs, Prims_nat r, void *s)
{
  return Crypto_Symmetric_Poly1305_Spec_finish(Crypto_Symmetric_Poly1305_Spec_poly(vs, r), s);
}

