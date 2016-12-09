#include "Crypto_Symmetric_Poly1305_Bignum.h"

void *Crypto_Symmetric_Poly1305_Bignum_prime = (void *)(uint8_t )0;

Prims_int Crypto_Symmetric_Poly1305_Bignum_w(uint32_t x0)
{
  return FStar_UInt32_v(x0);
}

void Crypto_Symmetric_Poly1305_Bignum_fsum_(uint64_t *a, uint64_t *b)
{
  uint64_t a0 = a[(uint32_t )0];
  uint64_t a1 = a[(uint32_t )1];
  uint64_t a2 = a[(uint32_t )2];
  uint64_t a3 = a[(uint32_t )3];
  uint64_t a4 = a[(uint32_t )4];
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b3 = b[(uint32_t )3];
  uint64_t b4 = b[(uint32_t )4];
  uint64_t ab0 = a0 + b0;
  uint64_t ab1 = a1 + b1;
  uint64_t ab2 = a2 + b2;
  uint64_t ab3 = a3 + b3;
  uint64_t ab4 = a4 + b4;
  a[(uint32_t )0] = ab0;
  a[(uint32_t )1] = ab1;
  a[(uint32_t )2] = ab2;
  a[(uint32_t )3] = ab3;
  a[(uint32_t )4] = ab4;
}

void Crypto_Symmetric_Poly1305_Bignum_fsum_0(uint64_t *a, uint64_t *b)
{
  Crypto_Symmetric_Poly1305_Bignum_fsum_(a, b);
  return;
}

void
Crypto_Symmetric_Poly1305_Bignum_update_9(
  uint64_t *c,
  uint64_t c0,
  uint64_t c1,
  uint64_t c2,
  uint64_t c3,
  uint64_t c4,
  uint64_t c5,
  uint64_t c6,
  uint64_t c7,
  uint64_t c8
)
{
  c[(uint32_t )0] = c0;
  c[(uint32_t )1] = c1;
  c[(uint32_t )2] = c2;
  c[(uint32_t )3] = c3;
  c[(uint32_t )4] = c4;
  c[(uint32_t )5] = c5;
  c[(uint32_t )6] = c6;
  c[(uint32_t )7] = c7;
  c[(uint32_t )8] = c8;
}

void
Crypto_Symmetric_Poly1305_Bignum_multiplication_0(
  uint64_t *c,
  uint64_t a0,
  uint64_t a1,
  uint64_t a2,
  uint64_t a3,
  uint64_t a4,
  uint64_t b0,
  uint64_t b1,
  uint64_t b2,
  uint64_t b3,
  uint64_t b4
)
{
  uint64_t ab00 = a0 * b0;
  uint64_t ab01 = a0 * b1;
  uint64_t ab02 = a0 * b2;
  uint64_t ab03 = a0 * b3;
  uint64_t ab04 = a0 * b4;
  uint64_t ab10 = a1 * b0;
  uint64_t ab11 = a1 * b1;
  uint64_t ab12 = a1 * b2;
  uint64_t ab13 = a1 * b3;
  uint64_t ab14 = a1 * b4;
  uint64_t ab20 = a2 * b0;
  uint64_t ab21 = a2 * b1;
  uint64_t ab22 = a2 * b2;
  uint64_t ab23 = a2 * b3;
  uint64_t ab24 = a2 * b4;
  uint64_t ab30 = a3 * b0;
  uint64_t ab31 = a3 * b1;
  uint64_t ab32 = a3 * b2;
  uint64_t ab33 = a3 * b3;
  uint64_t ab34 = a3 * b4;
  uint64_t ab40 = a4 * b0;
  uint64_t ab41 = a4 * b1;
  uint64_t ab42 = a4 * b2;
  uint64_t ab43 = a4 * b3;
  uint64_t ab44 = a4 * b4;
  uint64_t c0 = ab00;
  uint64_t c1 = ab01 + ab10;
  uint64_t c2 = ab02 + ab11 + ab20;
  uint64_t c3 = ab03 + ab12 + ab21 + ab30;
  uint64_t c4 = ab04 + ab13 + ab22 + ab31 + ab40;
  uint64_t c5 = ab14 + ab23 + ab32 + ab41;
  uint64_t c6 = ab24 + ab33 + ab42;
  uint64_t c7 = ab34 + ab43;
  uint64_t c8 = ab44;
  Crypto_Symmetric_Poly1305_Bignum_update_9(c, c0, c1, c2, c3, c4, c5, c6, c7, c8);
  return;
}

void Crypto_Symmetric_Poly1305_Bignum_multiplication_(uint64_t *c, uint64_t *a, uint64_t *b)
{
  uint64_t a0 = a[(uint32_t )0];
  uint64_t a1 = a[(uint32_t )1];
  uint64_t a2 = a[(uint32_t )2];
  uint64_t a3 = a[(uint32_t )3];
  uint64_t a4 = a[(uint32_t )4];
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b3 = b[(uint32_t )3];
  uint64_t b4 = b[(uint32_t )4];
  Crypto_Symmetric_Poly1305_Bignum_multiplication_0(c, a0, a1, a2, a3, a4, b0, b1, b2, b3, b4);
  return;
}

void Crypto_Symmetric_Poly1305_Bignum_multiplication(uint64_t *c, uint64_t *a, uint64_t *b)
{
  Crypto_Symmetric_Poly1305_Bignum_multiplication_(c, a, b);
  return;
}

uint64_t Crypto_Symmetric_Poly1305_Bignum_times_5(uint64_t b)
{
  return (b << (uint32_t )2) + b;
}

void Crypto_Symmetric_Poly1305_Bignum_freduce_degree_(uint64_t *b)
{
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b3 = b[(uint32_t )3];
  uint64_t b5 = b[(uint32_t )5];
  uint64_t b6 = b[(uint32_t )6];
  uint64_t b7 = b[(uint32_t )7];
  uint64_t b8 = b[(uint32_t )8];
  uint64_t b0_ = b0 + Crypto_Symmetric_Poly1305_Bignum_times_5(b5);
  uint64_t b1_ = b1 + Crypto_Symmetric_Poly1305_Bignum_times_5(b6);
  uint64_t b2_ = b2 + Crypto_Symmetric_Poly1305_Bignum_times_5(b7);
  uint64_t b3_ = b3 + Crypto_Symmetric_Poly1305_Bignum_times_5(b8);
  b[(uint32_t )0] = b0_;
  b[(uint32_t )1] = b1_;
  b[(uint32_t )2] = b2_;
  b[(uint32_t )3] = b3_;
}

void Crypto_Symmetric_Poly1305_Bignum_freduce_degree(uint64_t *b)
{
  Crypto_Symmetric_Poly1305_Bignum_freduce_degree_(b);
  return;
}

uint64_t Crypto_Symmetric_Poly1305_Bignum_mod2_26(uint64_t x)
{
  return x & (uint64_t )0x3ffffff;
}

uint64_t Crypto_Symmetric_Poly1305_Bignum_div2_26(uint64_t x)
{
  return x >> (uint32_t )26;
}

void
Crypto_Symmetric_Poly1305_Bignum_update_6(
  uint64_t *c,
  uint64_t c0,
  uint64_t c1,
  uint64_t c2,
  uint64_t c3,
  uint64_t c4,
  uint64_t c5
)
{
  c[(uint32_t )0] = c0;
  c[(uint32_t )1] = c1;
  c[(uint32_t )2] = c2;
  c[(uint32_t )3] = c3;
  c[(uint32_t )4] = c4;
  c[(uint32_t )5] = c5;
}

void
Crypto_Symmetric_Poly1305_Bignum_carry_1_0(
  uint64_t *b,
  uint64_t b0,
  uint64_t b1,
  uint64_t b2,
  uint64_t b3,
  uint64_t b4
)
{
  uint64_t b0_ = Crypto_Symmetric_Poly1305_Bignum_mod2_26(b0);
  uint64_t r0 = Crypto_Symmetric_Poly1305_Bignum_div2_26(b0);
  uint64_t b1_ = Crypto_Symmetric_Poly1305_Bignum_mod2_26(b1 + r0);
  uint64_t r1 = Crypto_Symmetric_Poly1305_Bignum_div2_26(b1 + r0);
  uint64_t b2_ = Crypto_Symmetric_Poly1305_Bignum_mod2_26(b2 + r1);
  uint64_t r2 = Crypto_Symmetric_Poly1305_Bignum_div2_26(b2 + r1);
  uint64_t b3_ = Crypto_Symmetric_Poly1305_Bignum_mod2_26(b3 + r2);
  uint64_t r3 = Crypto_Symmetric_Poly1305_Bignum_div2_26(b3 + r2);
  uint64_t b4_ = Crypto_Symmetric_Poly1305_Bignum_mod2_26(b4 + r3);
  uint64_t b5_ = Crypto_Symmetric_Poly1305_Bignum_div2_26(b4 + r3);
  Crypto_Symmetric_Poly1305_Bignum_update_6(b, b0_, b1_, b2_, b3_, b4_, b5_);
  return;
}

void Crypto_Symmetric_Poly1305_Bignum_carry_1_(uint64_t *b)
{
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b3 = b[(uint32_t )3];
  uint64_t b4 = b[(uint32_t )4];
  Crypto_Symmetric_Poly1305_Bignum_carry_1_0(b, b0, b1, b2, b3, b4);
  return;
}

void Crypto_Symmetric_Poly1305_Bignum_carry_1(uint64_t *b)
{
  Crypto_Symmetric_Poly1305_Bignum_carry_1_(b);
  return;
}

void Crypto_Symmetric_Poly1305_Bignum_carry_2_(uint64_t *b)
{
  Crypto_Symmetric_Poly1305_Bignum_carry_1_(b);
  return;
}

void Crypto_Symmetric_Poly1305_Bignum_carry_2(uint64_t *b)
{
  Crypto_Symmetric_Poly1305_Bignum_carry_2_(b);
  return;
}

void Crypto_Symmetric_Poly1305_Bignum_carry_top_(uint64_t *b)
{
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b5 = b[(uint32_t )5];
  b[(uint32_t )0] = b0 + Crypto_Symmetric_Poly1305_Bignum_times_5(b5);
}

void Crypto_Symmetric_Poly1305_Bignum_carry_top_1(uint64_t *b)
{
  Crypto_Symmetric_Poly1305_Bignum_carry_top_(b);
  return;
}

void Crypto_Symmetric_Poly1305_Bignum_carry_top_2(uint64_t *b)
{
  Crypto_Symmetric_Poly1305_Bignum_carry_top_(b);
  return;
}

void Crypto_Symmetric_Poly1305_Bignum_carry_0_to_1_(uint64_t *b)
{
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t b0_ = Crypto_Symmetric_Poly1305_Bignum_mod2_26(b0);
  uint64_t r0 = Crypto_Symmetric_Poly1305_Bignum_div2_26(b0);
  b[(uint32_t )0] = b0_;
  b[(uint32_t )1] = b1 + r0;
}

void Crypto_Symmetric_Poly1305_Bignum_carry_0_to_1(uint64_t *b)
{
  Crypto_Symmetric_Poly1305_Bignum_carry_0_to_1_(b);
  return;
}

void Crypto_Symmetric_Poly1305_Bignum_freduce_coefficients(uint64_t *b)
{
  Crypto_Symmetric_Poly1305_Bignum_carry_1(b);
  Crypto_Symmetric_Poly1305_Bignum_carry_top_1(b);
  Crypto_Symmetric_Poly1305_Bignum_carry_2(b);
  Crypto_Symmetric_Poly1305_Bignum_carry_top_2(b);
  Crypto_Symmetric_Poly1305_Bignum_carry_0_to_1(b);
  return;
}

void Crypto_Symmetric_Poly1305_Bignum_modulo(uint64_t *b)
{
  Crypto_Symmetric_Poly1305_Bignum_freduce_degree(b);
  Crypto_Symmetric_Poly1305_Bignum_freduce_coefficients(b);
  return;
}

void Crypto_Symmetric_Poly1305_Bignum_finalize(uint64_t *b)
{
  uint64_t mask_26 = (uint64_t )67108863;
  uint64_t mask2_26m5 = (uint64_t )67108859;
  uint64_t b0 = b[(uint32_t )0];
  uint64_t b1 = b[(uint32_t )1];
  uint64_t b2 = b[(uint32_t )2];
  uint64_t b3 = b[(uint32_t )3];
  uint64_t b4 = b[(uint32_t )4];
  uint64_t mask = FStar_UInt64_eq_mask(b4, mask_26);
  uint64_t mask4 = FStar_UInt64_eq_mask(b4, mask_26);
  uint64_t mask3 = FStar_UInt64_eq_mask(b3, mask_26);
  uint64_t mask2 = FStar_UInt64_eq_mask(b2, mask_26);
  uint64_t mask1 = FStar_UInt64_eq_mask(b1, mask_26);
  uint64_t mask0 = FStar_UInt64_gte_mask(b0, mask2_26m5);
  uint64_t mask5 = mask4 & mask3 & mask2 & mask1 & mask0;
  uint64_t b0_ = b0 - (mask2_26m5 & mask5);
  uint64_t b1_ = b1 - (b1 & mask5);
  uint64_t b2_ = b2 - (b2 & mask5);
  uint64_t b3_ = b3 - (b3 & mask5);
  uint64_t b4_ = b4 - (b4 & mask5);
  b[(uint32_t )0] = b0_;
  b[(uint32_t )1] = b1_;
  b[(uint32_t )2] = b2_;
  b[(uint32_t )3] = b3_;
  b[(uint32_t )4] = b4_;
}

