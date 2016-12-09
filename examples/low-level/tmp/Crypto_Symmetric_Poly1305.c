#include "Crypto_Symmetric_Poly1305.h"

void *Crypto_Symmetric_Poly1305_sel_word(FStar_HyperStack_mem h, uint8_t *b)
{
  return (void *)(uint8_t )0;
}

void *Crypto_Symmetric_Poly1305__read_word(uint32_t len, uint8_t *b, void *s, uint32_t i)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void *Crypto_Symmetric_Poly1305_read_word(uint32_t len, uint8_t *b)
{
  void *s0 = FStar_Seq_createEmpty((uint8_t )0);
  return Crypto_Symmetric_Poly1305__read_word(len, b, s0, (uint32_t )0);
}

Prims_nat Crypto_Symmetric_Poly1305_sel_elem(FStar_HyperStack_mem h, uint64_t *b)
{
  return (Prims_int )(uint8_t )0;
}

Prims_nat Crypto_Symmetric_Poly1305_sel_int(FStar_HyperStack_mem h, uint64_t *b)
{
  return (Prims_nat )(uint8_t )0;
}

void Crypto_Symmetric_Poly1305_lemma_bitweight_templ_values(Prims_nat n)
{
  return;
}

void
Crypto_Symmetric_Poly1305_lemma_eval_norm_is_bounded(
  FStar_HyperStack_mem ha,
  uint64_t *a,
  Prims_nat len
)
{
  return;
}

void
Crypto_Symmetric_Poly1305_lemma_elemB_equality(
  FStar_HyperStack_mem ha,
  FStar_HyperStack_mem hb,
  uint64_t *a,
  uint64_t *b,
  Prims_pos len
)
{
  return;
}

void
Crypto_Symmetric_Poly1305_lemma_toField_is_injective_0(
  FStar_HyperStack_mem ha,
  FStar_HyperStack_mem hb,
  uint64_t *a,
  uint64_t *b,
  Prims_nat len
)
{
  return;
}

void
Crypto_Symmetric_Poly1305_lemma_toField_is_injective(
  FStar_HyperStack_mem ha,
  FStar_HyperStack_mem hb,
  uint64_t *a,
  uint64_t *b
)
{
  return;
}

bool Crypto_Symmetric_Poly1305_print_elem(uint64_t *e, uint32_t i, uint32_t len)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void
Crypto_Symmetric_Poly1305_bound27_isSum(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  uint64_t *a,
  uint64_t *b
)
{
  return;
}

void
Crypto_Symmetric_Poly1305_lemma_sel_elem(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  uint64_t *acc,
  uint64_t *block,
  uint64_t *r
)
{
  return;
}

void Crypto_Symmetric_Poly1305_add_and_multiply(uint64_t *acc, uint64_t *block, uint64_t *r)
{
  Crypto_Symmetric_Poly1305_Bignum_fsum_0(acc, block);
  uint64_t tmp[9] = { 0 };
  Crypto_Symmetric_Poly1305_Bignum_multiplication(tmp, acc, r);
  Crypto_Symmetric_Poly1305_Bignum_modulo(tmp);
  memcpy(acc, tmp, (uint32_t )5 * sizeof tmp[0]);
}

void Crypto_Symmetric_Poly1305_zeroB(uint64_t *a)
{
  a[(uint32_t )0] = (uint64_t )0;
  a[(uint32_t )1] = (uint64_t )0;
  a[(uint32_t )2] = (uint64_t )0;
  a[(uint32_t )3] = (uint64_t )0;
  a[(uint32_t )4] = (uint64_t )0;
}

uint64_t Crypto_Symmetric_Poly1305_mk_mask(uint32_t nbits)
{
  return ((uint64_t )1 << nbits) - (uint64_t )1;
}

void
Crypto_Symmetric_Poly1305_lemma_toField_1(
  uint64_t *b,
  uint8_t *s,
  FStar_HyperStack_mem h,
  uint64_t n0,
  uint64_t n1,
  uint64_t n2,
  uint64_t n3
)
{
  return;
}

void
Crypto_Symmetric_Poly1305_upd_elemB(
  uint64_t *b,
  uint64_t n0,
  uint64_t n1,
  uint64_t n2,
  uint64_t n3,
  uint64_t n4
)
{
  b[(uint32_t )0] = n0;
  b[(uint32_t )1] = n1;
  b[(uint32_t )2] = n2;
  b[(uint32_t )3] = n3;
  b[(uint32_t )4] = n4;
}

void
Crypto_Symmetric_Poly1305_lemma_toField_2(
  uint64_t n0,
  uint64_t n1,
  uint64_t n2,
  uint64_t n3,
  uint64_t n0_,
  uint64_t n1_,
  uint64_t n2_,
  uint64_t n3_,
  uint64_t n4_
)
{
  return;
}

void
Crypto_Symmetric_Poly1305_lemma_toField_3(
  uint64_t n0,
  uint64_t n1,
  uint64_t n2,
  uint64_t n3,
  uint64_t n0_,
  uint64_t n1_,
  uint64_t n2_,
  uint64_t n3_,
  uint64_t n4_
)
{
  return;
}

void Crypto_Symmetric_Poly1305_sel_int_sel_elem(FStar_HyperStack_mem h, uint64_t *a, void *w)
{
  return;
}

void Crypto_Symmetric_Poly1305_toField(uint64_t *b, uint8_t *s)
{
  uint64_t mask_26 = Crypto_Symmetric_Poly1305_mk_mask((uint32_t )26);
  uint8_t *s0 = s + (uint32_t )0;
  uint8_t *s1 = s + (uint32_t )4;
  uint8_t *s2 = s + (uint32_t )8;
  uint8_t *s3 = s + (uint32_t )12;
  uint32_t n00 = Buffer_Utils_uint32_of_bytes(s0);
  uint32_t n10 = Buffer_Utils_uint32_of_bytes(s1);
  uint32_t n20 = Buffer_Utils_uint32_of_bytes(s2);
  uint32_t n30 = Buffer_Utils_uint32_of_bytes(s3);
  uint64_t n0 = (uint64_t )n00;
  uint64_t n1 = (uint64_t )n10;
  uint64_t n2 = (uint64_t )n20;
  uint64_t n3 = (uint64_t )n30;
  uint64_t n0_ = n0 & mask_26;
  uint64_t n1_ = n0 >> (uint32_t )26 | n1 << (uint32_t )6 & mask_26;
  uint64_t n2_ = n1 >> (uint32_t )20 | n2 << (uint32_t )12 & mask_26;
  uint64_t n3_ = n2 >> (uint32_t )14 | n3 << (uint32_t )18 & mask_26;
  uint64_t n4_ = n3 >> (uint32_t )8;
  Crypto_Symmetric_Poly1305_upd_elemB(b, n0_, n1_, n2_, n3_, n4_);
  return;
}

void Crypto_Symmetric_Poly1305_lemma_toField_plus_2_128_0(FStar_HyperStack_mem ha, uint64_t *a)
{
  return;
}

void Crypto_Symmetric_Poly1305_lemma_toField_plus_2_128_1()
{
  return;
}

void
Crypto_Symmetric_Poly1305_lemma_toField_plus_2_128(
  FStar_HyperStack_mem ha,
  uint64_t *a,
  FStar_HyperStack_mem hb,
  uint64_t *b
)
{
  return;
}

uint64_t Crypto_Symmetric_Poly1305_add_2_24(uint64_t x)
{
  return x + ((uint64_t )1 << (uint32_t )24);
}

void Crypto_Symmetric_Poly1305_toField_plus_2_128(uint64_t *b, uint8_t *s)
{
  Crypto_Symmetric_Poly1305_toField(b, s);
  uint64_t b4 = b[(uint32_t )4];
  uint64_t b4_ = Crypto_Symmetric_Poly1305_add_2_24(b4);
  b[(uint32_t )4] = b4_;
}

void Crypto_Symmetric_Poly1305_toField_plus(uint32_t len, uint64_t *a, uint8_t *b)
{
  uint8_t n[16] = { 0 };
  memcpy(n, b, len * sizeof b[0]);
  n[len] = (uint8_t )1;
  Crypto_Symmetric_Poly1305_toField(a, n);
}

void
Crypto_Symmetric_Poly1305_upd_wordB_16(
  uint8_t *s,
  uint8_t s0,
  uint8_t s1,
  uint8_t s2,
  uint8_t s3,
  uint8_t s4,
  uint8_t s5,
  uint8_t s6,
  uint8_t s7,
  uint8_t s8,
  uint8_t s9,
  uint8_t s10,
  uint8_t s11,
  uint8_t s12,
  uint8_t s13,
  uint8_t s14,
  uint8_t s15
)
{
  s[(uint32_t )0] = s0;
  s[(uint32_t )1] = s1;
  s[(uint32_t )2] = s2;
  s[(uint32_t )3] = s3;
  s[(uint32_t )4] = s4;
  s[(uint32_t )5] = s5;
  s[(uint32_t )6] = s6;
  s[(uint32_t )7] = s7;
  s[(uint32_t )8] = s8;
  s[(uint32_t )9] = s9;
  s[(uint32_t )10] = s10;
  s[(uint32_t )11] = s11;
  s[(uint32_t )12] = s12;
  s[(uint32_t )13] = s13;
  s[(uint32_t )14] = s14;
  s[(uint32_t )15] = s15;
}

void Crypto_Symmetric_Poly1305_trunc1305(uint64_t *a, uint8_t *b)
{
  Crypto_Symmetric_Poly1305_Bignum_finalize(a);
  uint64_t a0 = a[(uint32_t )0];
  uint64_t a1 = a[(uint32_t )1];
  uint64_t a2 = a[(uint32_t )2];
  uint64_t a3 = a[(uint32_t )3];
  uint64_t a4 = a[(uint32_t )4];
  uint8_t b0 = (uint8_t )a0;
  uint8_t b1 = (uint8_t )(a0 >> (uint32_t )8);
  uint8_t b2 = (uint8_t )(a0 >> (uint32_t )16);
  uint8_t b3 = (uint8_t )(a0 >> (uint32_t )24 | a1 << (uint32_t )2);
  uint8_t b4 = (uint8_t )(a1 >> (uint32_t )6);
  uint8_t b5 = (uint8_t )(a1 >> (uint32_t )14);
  uint8_t b6 = (uint8_t )(a1 >> (uint32_t )22 | a2 << (uint32_t )4);
  uint8_t b7 = (uint8_t )(a2 >> (uint32_t )4);
  uint8_t b8 = (uint8_t )(a2 >> (uint32_t )12);
  uint8_t b9 = (uint8_t )(a2 >> (uint32_t )20 | a3 << (uint32_t )6);
  uint8_t b10 = (uint8_t )(a3 >> (uint32_t )2);
  uint8_t b11 = (uint8_t )(a3 >> (uint32_t )10);
  uint8_t b12 = (uint8_t )(a3 >> (uint32_t )18);
  uint8_t b13 = (uint8_t )a4;
  uint8_t b14 = (uint8_t )(a4 >> (uint32_t )8);
  uint8_t b15 = (uint8_t )(a4 >> (uint32_t )16);
  Crypto_Symmetric_Poly1305_upd_wordB_16(b,
    b0,
    b1,
    b2,
    b3,
    b4,
    b5,
    b6,
    b7,
    b8,
    b9,
    b10,
    b11,
    b12,
    b13,
    b14,
    b15);
  return;
}

void Crypto_Symmetric_Poly1305_fix(uint8_t *r, uint32_t i, uint8_t mask)
{
  uint8_t _0_124 = r[i];
  uint8_t _0_125 = _0_124 & mask;
  r[i] = _0_125;
}

void Crypto_Symmetric_Poly1305_clamp(uint8_t *r)
{
  Crypto_Symmetric_Poly1305_fix(r, (uint32_t )3, (uint8_t )15);
  Crypto_Symmetric_Poly1305_fix(r, (uint32_t )7, (uint8_t )15);
  Crypto_Symmetric_Poly1305_fix(r, (uint32_t )11, (uint8_t )15);
  Crypto_Symmetric_Poly1305_fix(r, (uint32_t )15, (uint8_t )15);
  Crypto_Symmetric_Poly1305_fix(r, (uint32_t )4, (uint8_t )252);
  Crypto_Symmetric_Poly1305_fix(r, (uint32_t )8, (uint8_t )252);
  Crypto_Symmetric_Poly1305_fix(r, (uint32_t )12, (uint8_t )252);
  return;
}

void Crypto_Symmetric_Poly1305_poly1305_init(uint64_t *r, uint8_t *s, uint8_t *key)
{
  uint8_t r_16[16] = { 0 };
  memcpy(r_16, key, (uint32_t )16 * sizeof key[0]);
  memcpy(s, key + (uint32_t )16, (uint32_t )16 * sizeof key[0]);
  Crypto_Symmetric_Poly1305_clamp(r_16);
  Crypto_Symmetric_Poly1305_toField(r, r_16);
}

void Crypto_Symmetric_Poly1305_poly1305_start(uint64_t *a)
{
  Crypto_Symmetric_Poly1305_zeroB(a);
  return;
}

void *Crypto_Symmetric_Poly1305_ilog()
{
  return (uint8_t )0;
}

void Crypto_Symmetric_Poly1305_add_word(uint8_t *a, uint8_t *b)
{
  uint32_t x0 = Buffer_Utils_uint32_of_bytes(a + (uint32_t )0);
  uint64_t a04 = (uint64_t )x0;
  uint32_t x1 = Buffer_Utils_uint32_of_bytes(a + (uint32_t )4);
  uint64_t a48 = (uint64_t )x1;
  uint32_t x2 = Buffer_Utils_uint32_of_bytes(a + (uint32_t )8);
  uint64_t a812 = (uint64_t )x2;
  uint32_t x3 = Buffer_Utils_uint32_of_bytes(a + (uint32_t )12);
  uint64_t a1216 = (uint64_t )x3;
  uint32_t x4 = Buffer_Utils_uint32_of_bytes(b + (uint32_t )0);
  uint64_t b04 = (uint64_t )x4;
  uint32_t x5 = Buffer_Utils_uint32_of_bytes(b + (uint32_t )4);
  uint64_t b48 = (uint64_t )x5;
  uint32_t x6 = Buffer_Utils_uint32_of_bytes(b + (uint32_t )8);
  uint64_t b812 = (uint64_t )x6;
  uint32_t x = Buffer_Utils_uint32_of_bytes(b + (uint32_t )12);
  uint64_t b1216 = (uint64_t )x;
  uint64_t z0 = a04 + b04;
  uint64_t z1 = a48 + b48 + (z0 >> (uint32_t )32);
  uint64_t z2 = a812 + b812 + (z1 >> (uint32_t )32);
  uint64_t z3 = a1216 + b1216 + (z2 >> (uint32_t )32);
  uint32_t z0_ = (uint32_t )z0;
  uint32_t z1_ = (uint32_t )z1;
  uint32_t z2_ = (uint32_t )z2;
  uint32_t z3_ = (uint32_t )z3;
  Buffer_Utils_bytes_of_uint32(a + (uint32_t )0, z0_);
  Buffer_Utils_bytes_of_uint32(a + (uint32_t )4, z1_);
  Buffer_Utils_bytes_of_uint32(a + (uint32_t )8, z2_);
  Buffer_Utils_bytes_of_uint32(a + (uint32_t )12, z3_);
  return;
}

void Crypto_Symmetric_Poly1305_poly1305_finish(uint8_t *tag, uint64_t *acc, uint8_t *s)
{
  Crypto_Symmetric_Poly1305_trunc1305(acc, tag);
  Crypto_Symmetric_Poly1305_add_word(tag, s);
  return;
}

