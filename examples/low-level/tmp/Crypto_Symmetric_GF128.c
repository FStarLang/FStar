#include "Crypto_Symmetric_GF128.h"

uint32_t Crypto_Symmetric_GF128_len = (uint32_t )16;

void Crypto_Symmetric_GF128_gf128_add_loop(uint8_t *a, uint8_t *b, uint32_t dep)
{
  if (dep == (uint32_t )0)
    return;
  else
  {
    uint32_t i = dep - (uint32_t )1;
    Crypto_Symmetric_GF128_gf128_add_loop(a, b, i);
    uint8_t _0_127 = a[i];
    uint8_t _0_126 = b[i];
    uint8_t _0_128 = _0_127 ^ _0_126;
    a[i] = _0_128;
  }
}

void Crypto_Symmetric_GF128_gf128_add(uint8_t *a, uint8_t *b)
{
  Crypto_Symmetric_GF128_gf128_add_loop(a, b, Crypto_Symmetric_GF128_len);
  return;
}

void Crypto_Symmetric_GF128_gf128_shift_right_loop(uint8_t *a, uint32_t dep)
{
  if (dep == (uint32_t )0)
  {
    uint8_t _0_129 = a[(uint32_t )0];
    uint8_t _0_130 = _0_129 >> (uint32_t )1;
    a[(uint32_t )0] = _0_130;
  }
  else
  {
    uint32_t i = dep - (uint32_t )1;
    uint8_t _0_131 = a[i];
    uint8_t _0_134 = _0_131 << (uint32_t )7;
    uint8_t _0_132 = a[dep];
    uint8_t _0_133 = _0_132 >> (uint32_t )1;
    uint8_t _0_135 = _0_134 + _0_133;
    a[dep] = _0_135;
    Crypto_Symmetric_GF128_gf128_shift_right_loop(a, i);
    return;
  }
}

void Crypto_Symmetric_GF128_gf128_shift_right(uint8_t *a)
{
  Crypto_Symmetric_GF128_gf128_shift_right_loop(a, (uint32_t )15);
  return;
}

uint8_t Crypto_Symmetric_GF128_ith_bit_mask(uint8_t num, uint32_t i)
{
  return FStar_UInt8_eq_mask(num & (uint8_t )128 >> i, (uint8_t )128 >> i);
}

void Crypto_Symmetric_GF128_apply_mask_loop(uint8_t *a, uint8_t *m, uint8_t msk, uint32_t dep)
{
  if (dep != (uint32_t )0)
  {
    uint32_t i = dep - (uint32_t )1;
    uint8_t _0_136 = a[i];
    uint8_t _0_137 = _0_136 & msk;
    m[i] = _0_137;
    Crypto_Symmetric_GF128_apply_mask_loop(a, m, msk, i);
    return;
  }
  else
    return;
}

void Crypto_Symmetric_GF128_apply_mask(uint8_t *a, uint8_t *m, uint8_t msk)
{
  Crypto_Symmetric_GF128_apply_mask_loop(a, m, msk, Crypto_Symmetric_GF128_len);
  return;
}

uint8_t Crypto_Symmetric_GF128_r_mul = (uint8_t )225;

void Crypto_Symmetric_GF128_gf128_mul_loop(uint8_t *a, uint8_t *b, uint8_t *tmp, uint32_t dep)
{
  if (dep != (uint32_t )128)
  {
    uint8_t *r = tmp + (uint32_t )0;
    uint8_t *m = tmp + Crypto_Symmetric_GF128_len;
    uint8_t num0 = b[dep / (uint32_t )8];
    uint8_t msk = Crypto_Symmetric_GF128_ith_bit_mask(num0, dep % (uint32_t )8);
    Crypto_Symmetric_GF128_apply_mask(a, m, msk);
    Crypto_Symmetric_GF128_gf128_add(r, m);
    uint8_t num1 = a[(uint32_t )15];
    uint8_t msk0 = Crypto_Symmetric_GF128_ith_bit_mask(num1, (uint32_t )7);
    Crypto_Symmetric_GF128_gf128_shift_right(a);
    uint8_t num = a[(uint32_t )0];
    a[(uint32_t )0] = num ^ msk0 & Crypto_Symmetric_GF128_r_mul;
    Crypto_Symmetric_GF128_gf128_mul_loop(a, b, tmp, dep + (uint32_t )1);
    return;
  }
  else
    return;
}

void Crypto_Symmetric_GF128_gf128_mul(uint8_t *a, uint8_t *b)
{
  uint8_t tmp[32] = { 0 };
  Crypto_Symmetric_GF128_gf128_mul_loop(a, b, tmp, (uint32_t )0);
  memcpy(a, tmp, (uint32_t )16 * sizeof tmp[0]);
}

void Crypto_Symmetric_GF128_add_and_multiply(uint8_t *acc, uint8_t *block, uint8_t *k)
{
  Crypto_Symmetric_GF128_gf128_add(acc, block);
  Crypto_Symmetric_GF128_gf128_mul(acc, k);
  return;
}

void Crypto_Symmetric_GF128_finish(uint8_t *a, uint8_t *s)
{
  Crypto_Symmetric_GF128_gf128_add(a, s);
  return;
}

void
Crypto_Symmetric_GF128_ghash_loop_(
  uint8_t *tag,
  uint8_t *auth_key,
  uint8_t *str,
  uint32_t len,
  uint32_t dep
)
{
  uint8_t last[16] = { 0 };
  memcpy(last, str + dep, (len - dep) * sizeof str[0]);
  Crypto_Symmetric_GF128_add_and_multiply(tag, last, auth_key);
}

void
Crypto_Symmetric_GF128_ghash_loop(
  uint8_t *tag,
  uint8_t *auth_key,
  uint8_t *str,
  uint32_t len,
  uint32_t dep
)
{
  uint32_t rest = len - dep;
  if (rest != (uint32_t )0)
    if ((uint32_t )16 >= rest)
    {
      Crypto_Symmetric_GF128_ghash_loop_(tag, auth_key, str, len, dep);
      return;
    }
    else
    {
      uint32_t next = dep + (uint32_t )16;
      uint8_t *si = str + dep;
      Crypto_Symmetric_GF128_add_and_multiply(tag, si, auth_key);
      Crypto_Symmetric_GF128_ghash_loop(tag, auth_key, str, len, next);
      return;
    }
  else
    return;
}

void Crypto_Symmetric_GF128_mk_len_info(uint8_t *len_info, uint32_t len_1, uint32_t len_2)
{
  uint8_t last = (uint8_t )len_1 << (uint32_t )3;
  len_info[(uint32_t )7] = last;
  uint32_t len_10 = len_1 >> (uint32_t )5;
  len_info[(uint32_t )6] = (uint8_t )len_10;
  uint32_t len_11 = len_10 >> (uint32_t )8;
  len_info[(uint32_t )5] = (uint8_t )len_11;
  uint32_t len_12 = len_11 >> (uint32_t )8;
  len_info[(uint32_t )4] = (uint8_t )len_12;
  uint32_t len_13 = len_12 >> (uint32_t )8;
  len_info[(uint32_t )3] = (uint8_t )len_13;
  uint8_t last0 = (uint8_t )len_2 << (uint32_t )3;
  len_info[(uint32_t )15] = last0;
  uint32_t len_20 = len_2 >> (uint32_t )5;
  len_info[(uint32_t )14] = (uint8_t )len_20;
  uint32_t len_21 = len_20 >> (uint32_t )8;
  len_info[(uint32_t )13] = (uint8_t )len_21;
  uint32_t len_22 = len_21 >> (uint32_t )8;
  len_info[(uint32_t )12] = (uint8_t )len_22;
  uint32_t len_23 = len_22 >> (uint32_t )8;
  len_info[(uint32_t )11] = (uint8_t )len_23;
}

void
Crypto_Symmetric_GF128_ghash(
  uint8_t *k,
  uint8_t *ad,
  uint32_t adlen,
  uint8_t *ciphertext,
  uint32_t len,
  uint8_t *tag
)
{
  uint8_t len_info[16] = { 0 };
  Crypto_Symmetric_GF128_mk_len_info(len_info, adlen, len);
  for (uintmax_t i = 0; i < (uint32_t )16; ++i)
    tag[i] = (uint8_t )0;
  Crypto_Symmetric_GF128_ghash_loop(tag, k, ad, adlen, (uint32_t )0);
  Crypto_Symmetric_GF128_ghash_loop(tag, k, ciphertext, len, (uint32_t )0);
  Crypto_Symmetric_GF128_add_and_multiply(tag, len_info, k);
}

