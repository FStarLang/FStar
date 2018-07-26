/* MIT License
 *
 * Copyright (c) 2016-2018 INRIA and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "Hacl_SHA2_256.h"

static void
Hacl_Hash_Lib_LoadStore_uint32s_from_be_bytes(uint32_t *output, uint8_t *input, uint32_t len)
{
  for (uint32_t i = (uint32_t)0U; i < len; i = i + (uint32_t)1U)
  {
    uint8_t *x0 = input + (uint32_t)4U * i;
    uint32_t inputi = load32_be(x0);
    output[i] = inputi;
  }
}

static void
Hacl_Hash_Lib_LoadStore_uint32s_to_be_bytes(uint8_t *output, uint32_t *input, uint32_t len)
{
  for (uint32_t i = (uint32_t)0U; i < len; i = i + (uint32_t)1U)
  {
    uint32_t hd1 = input[i];
    uint8_t *x0 = output + (uint32_t)4U * i;
    store32_be(x0, hd1);
  }
}

static void Hacl_Impl_SHA2_256_assign_k(uint32_t *b)
{
  uint32_t *b_hd = b;
  uint32_t *b_tl = b + (uint32_t)1U;
  b_hd[0U] = (uint32_t)0x428a2f98U;
  uint32_t *b_hd1 = b_tl;
  uint32_t *b_tl1 = b_tl + (uint32_t)1U;
  b_hd1[0U] = (uint32_t)0x71374491U;
  uint32_t *b_hd2 = b_tl1;
  uint32_t *b_tl2 = b_tl1 + (uint32_t)1U;
  b_hd2[0U] = (uint32_t)0xb5c0fbcfU;
  uint32_t *b_hd3 = b_tl2;
  uint32_t *b_tl3 = b_tl2 + (uint32_t)1U;
  b_hd3[0U] = (uint32_t)0xe9b5dba5U;
  uint32_t *b_hd4 = b_tl3;
  uint32_t *b_tl4 = b_tl3 + (uint32_t)1U;
  b_hd4[0U] = (uint32_t)0x3956c25bU;
  uint32_t *b_hd5 = b_tl4;
  uint32_t *b_tl5 = b_tl4 + (uint32_t)1U;
  b_hd5[0U] = (uint32_t)0x59f111f1U;
  uint32_t *b_hd6 = b_tl5;
  uint32_t *b_tl6 = b_tl5 + (uint32_t)1U;
  b_hd6[0U] = (uint32_t)0x923f82a4U;
  uint32_t *b_hd7 = b_tl6;
  uint32_t *b_tl7 = b_tl6 + (uint32_t)1U;
  b_hd7[0U] = (uint32_t)0xab1c5ed5U;
  uint32_t *b_hd8 = b_tl7;
  uint32_t *b_tl8 = b_tl7 + (uint32_t)1U;
  b_hd8[0U] = (uint32_t)0xd807aa98U;
  uint32_t *b_hd9 = b_tl8;
  uint32_t *b_tl9 = b_tl8 + (uint32_t)1U;
  b_hd9[0U] = (uint32_t)0x12835b01U;
  uint32_t *b_hd10 = b_tl9;
  uint32_t *b_tl10 = b_tl9 + (uint32_t)1U;
  b_hd10[0U] = (uint32_t)0x243185beU;
  uint32_t *b_hd11 = b_tl10;
  uint32_t *b_tl11 = b_tl10 + (uint32_t)1U;
  b_hd11[0U] = (uint32_t)0x550c7dc3U;
  uint32_t *b_hd12 = b_tl11;
  uint32_t *b_tl12 = b_tl11 + (uint32_t)1U;
  b_hd12[0U] = (uint32_t)0x72be5d74U;
  uint32_t *b_hd13 = b_tl12;
  uint32_t *b_tl13 = b_tl12 + (uint32_t)1U;
  b_hd13[0U] = (uint32_t)0x80deb1feU;
  uint32_t *b_hd14 = b_tl13;
  uint32_t *b_tl14 = b_tl13 + (uint32_t)1U;
  b_hd14[0U] = (uint32_t)0x9bdc06a7U;
  uint32_t *b_hd15 = b_tl14;
  uint32_t *b_tl15 = b_tl14 + (uint32_t)1U;
  b_hd15[0U] = (uint32_t)0xc19bf174U;
  uint32_t *b_hd16 = b_tl15;
  uint32_t *b_tl16 = b_tl15 + (uint32_t)1U;
  b_hd16[0U] = (uint32_t)0xe49b69c1U;
  uint32_t *b_hd17 = b_tl16;
  uint32_t *b_tl17 = b_tl16 + (uint32_t)1U;
  b_hd17[0U] = (uint32_t)0xefbe4786U;
  uint32_t *b_hd18 = b_tl17;
  uint32_t *b_tl18 = b_tl17 + (uint32_t)1U;
  b_hd18[0U] = (uint32_t)0x0fc19dc6U;
  uint32_t *b_hd19 = b_tl18;
  uint32_t *b_tl19 = b_tl18 + (uint32_t)1U;
  b_hd19[0U] = (uint32_t)0x240ca1ccU;
  uint32_t *b_hd20 = b_tl19;
  uint32_t *b_tl20 = b_tl19 + (uint32_t)1U;
  b_hd20[0U] = (uint32_t)0x2de92c6fU;
  uint32_t *b_hd21 = b_tl20;
  uint32_t *b_tl21 = b_tl20 + (uint32_t)1U;
  b_hd21[0U] = (uint32_t)0x4a7484aaU;
  uint32_t *b_hd22 = b_tl21;
  uint32_t *b_tl22 = b_tl21 + (uint32_t)1U;
  b_hd22[0U] = (uint32_t)0x5cb0a9dcU;
  uint32_t *b_hd23 = b_tl22;
  uint32_t *b_tl23 = b_tl22 + (uint32_t)1U;
  b_hd23[0U] = (uint32_t)0x76f988daU;
  uint32_t *b_hd24 = b_tl23;
  uint32_t *b_tl24 = b_tl23 + (uint32_t)1U;
  b_hd24[0U] = (uint32_t)0x983e5152U;
  uint32_t *b_hd25 = b_tl24;
  uint32_t *b_tl25 = b_tl24 + (uint32_t)1U;
  b_hd25[0U] = (uint32_t)0xa831c66dU;
  uint32_t *b_hd26 = b_tl25;
  uint32_t *b_tl26 = b_tl25 + (uint32_t)1U;
  b_hd26[0U] = (uint32_t)0xb00327c8U;
  uint32_t *b_hd27 = b_tl26;
  uint32_t *b_tl27 = b_tl26 + (uint32_t)1U;
  b_hd27[0U] = (uint32_t)0xbf597fc7U;
  uint32_t *b_hd28 = b_tl27;
  uint32_t *b_tl28 = b_tl27 + (uint32_t)1U;
  b_hd28[0U] = (uint32_t)0xc6e00bf3U;
  uint32_t *b_hd29 = b_tl28;
  uint32_t *b_tl29 = b_tl28 + (uint32_t)1U;
  b_hd29[0U] = (uint32_t)0xd5a79147U;
  uint32_t *b_hd30 = b_tl29;
  uint32_t *b_tl30 = b_tl29 + (uint32_t)1U;
  b_hd30[0U] = (uint32_t)0x06ca6351U;
  uint32_t *b_hd31 = b_tl30;
  uint32_t *b_tl31 = b_tl30 + (uint32_t)1U;
  b_hd31[0U] = (uint32_t)0x14292967U;
  uint32_t *b_hd32 = b_tl31;
  uint32_t *b_tl32 = b_tl31 + (uint32_t)1U;
  b_hd32[0U] = (uint32_t)0x27b70a85U;
  uint32_t *b_hd33 = b_tl32;
  uint32_t *b_tl33 = b_tl32 + (uint32_t)1U;
  b_hd33[0U] = (uint32_t)0x2e1b2138U;
  uint32_t *b_hd34 = b_tl33;
  uint32_t *b_tl34 = b_tl33 + (uint32_t)1U;
  b_hd34[0U] = (uint32_t)0x4d2c6dfcU;
  uint32_t *b_hd35 = b_tl34;
  uint32_t *b_tl35 = b_tl34 + (uint32_t)1U;
  b_hd35[0U] = (uint32_t)0x53380d13U;
  uint32_t *b_hd36 = b_tl35;
  uint32_t *b_tl36 = b_tl35 + (uint32_t)1U;
  b_hd36[0U] = (uint32_t)0x650a7354U;
  uint32_t *b_hd37 = b_tl36;
  uint32_t *b_tl37 = b_tl36 + (uint32_t)1U;
  b_hd37[0U] = (uint32_t)0x766a0abbU;
  uint32_t *b_hd38 = b_tl37;
  uint32_t *b_tl38 = b_tl37 + (uint32_t)1U;
  b_hd38[0U] = (uint32_t)0x81c2c92eU;
  uint32_t *b_hd39 = b_tl38;
  uint32_t *b_tl39 = b_tl38 + (uint32_t)1U;
  b_hd39[0U] = (uint32_t)0x92722c85U;
  uint32_t *b_hd40 = b_tl39;
  uint32_t *b_tl40 = b_tl39 + (uint32_t)1U;
  b_hd40[0U] = (uint32_t)0xa2bfe8a1U;
  uint32_t *b_hd41 = b_tl40;
  uint32_t *b_tl41 = b_tl40 + (uint32_t)1U;
  b_hd41[0U] = (uint32_t)0xa81a664bU;
  uint32_t *b_hd42 = b_tl41;
  uint32_t *b_tl42 = b_tl41 + (uint32_t)1U;
  b_hd42[0U] = (uint32_t)0xc24b8b70U;
  uint32_t *b_hd43 = b_tl42;
  uint32_t *b_tl43 = b_tl42 + (uint32_t)1U;
  b_hd43[0U] = (uint32_t)0xc76c51a3U;
  uint32_t *b_hd44 = b_tl43;
  uint32_t *b_tl44 = b_tl43 + (uint32_t)1U;
  b_hd44[0U] = (uint32_t)0xd192e819U;
  uint32_t *b_hd45 = b_tl44;
  uint32_t *b_tl45 = b_tl44 + (uint32_t)1U;
  b_hd45[0U] = (uint32_t)0xd6990624U;
  uint32_t *b_hd46 = b_tl45;
  uint32_t *b_tl46 = b_tl45 + (uint32_t)1U;
  b_hd46[0U] = (uint32_t)0xf40e3585U;
  uint32_t *b_hd47 = b_tl46;
  uint32_t *b_tl47 = b_tl46 + (uint32_t)1U;
  b_hd47[0U] = (uint32_t)0x106aa070U;
  uint32_t *b_hd48 = b_tl47;
  uint32_t *b_tl48 = b_tl47 + (uint32_t)1U;
  b_hd48[0U] = (uint32_t)0x19a4c116U;
  uint32_t *b_hd49 = b_tl48;
  uint32_t *b_tl49 = b_tl48 + (uint32_t)1U;
  b_hd49[0U] = (uint32_t)0x1e376c08U;
  uint32_t *b_hd50 = b_tl49;
  uint32_t *b_tl50 = b_tl49 + (uint32_t)1U;
  b_hd50[0U] = (uint32_t)0x2748774cU;
  uint32_t *b_hd51 = b_tl50;
  uint32_t *b_tl51 = b_tl50 + (uint32_t)1U;
  b_hd51[0U] = (uint32_t)0x34b0bcb5U;
  uint32_t *b_hd52 = b_tl51;
  uint32_t *b_tl52 = b_tl51 + (uint32_t)1U;
  b_hd52[0U] = (uint32_t)0x391c0cb3U;
  uint32_t *b_hd53 = b_tl52;
  uint32_t *b_tl53 = b_tl52 + (uint32_t)1U;
  b_hd53[0U] = (uint32_t)0x4ed8aa4aU;
  uint32_t *b_hd54 = b_tl53;
  uint32_t *b_tl54 = b_tl53 + (uint32_t)1U;
  b_hd54[0U] = (uint32_t)0x5b9cca4fU;
  uint32_t *b_hd55 = b_tl54;
  uint32_t *b_tl55 = b_tl54 + (uint32_t)1U;
  b_hd55[0U] = (uint32_t)0x682e6ff3U;
  uint32_t *b_hd56 = b_tl55;
  uint32_t *b_tl56 = b_tl55 + (uint32_t)1U;
  b_hd56[0U] = (uint32_t)0x748f82eeU;
  uint32_t *b_hd57 = b_tl56;
  uint32_t *b_tl57 = b_tl56 + (uint32_t)1U;
  b_hd57[0U] = (uint32_t)0x78a5636fU;
  uint32_t *b_hd58 = b_tl57;
  uint32_t *b_tl58 = b_tl57 + (uint32_t)1U;
  b_hd58[0U] = (uint32_t)0x84c87814U;
  uint32_t *b_hd59 = b_tl58;
  uint32_t *b_tl59 = b_tl58 + (uint32_t)1U;
  b_hd59[0U] = (uint32_t)0x8cc70208U;
  uint32_t *b_hd60 = b_tl59;
  uint32_t *b_tl60 = b_tl59 + (uint32_t)1U;
  b_hd60[0U] = (uint32_t)0x90befffaU;
  uint32_t *b_hd61 = b_tl60;
  uint32_t *b_tl61 = b_tl60 + (uint32_t)1U;
  b_hd61[0U] = (uint32_t)0xa4506cebU;
  uint32_t *b_hd62 = b_tl61;
  uint32_t *b_tl62 = b_tl61 + (uint32_t)1U;
  b_hd62[0U] = (uint32_t)0xbef9a3f7U;
  uint32_t *b_hd63 = b_tl62;
  b_hd63[0U] = (uint32_t)0xc67178f2U;
}

static void Hacl_Impl_SHA2_256_constants_set_k(uint32_t *k1)
{
  Hacl_Impl_SHA2_256_assign_k(k1);
}

static void Hacl_Impl_SHA2_256_assign_h0(uint32_t *b)
{
  uint32_t *b_hd = b;
  uint32_t *b_tl = b + (uint32_t)1U;
  b_hd[0U] = (uint32_t)0x6a09e667U;
  uint32_t *b_hd1 = b_tl;
  uint32_t *b_tl1 = b_tl + (uint32_t)1U;
  b_hd1[0U] = (uint32_t)0xbb67ae85U;
  uint32_t *b_hd2 = b_tl1;
  uint32_t *b_tl2 = b_tl1 + (uint32_t)1U;
  b_hd2[0U] = (uint32_t)0x3c6ef372U;
  uint32_t *b_hd3 = b_tl2;
  uint32_t *b_tl3 = b_tl2 + (uint32_t)1U;
  b_hd3[0U] = (uint32_t)0xa54ff53aU;
  uint32_t *b_hd4 = b_tl3;
  uint32_t *b_tl4 = b_tl3 + (uint32_t)1U;
  b_hd4[0U] = (uint32_t)0x510e527fU;
  uint32_t *b_hd5 = b_tl4;
  uint32_t *b_tl5 = b_tl4 + (uint32_t)1U;
  b_hd5[0U] = (uint32_t)0x9b05688cU;
  uint32_t *b_hd6 = b_tl5;
  uint32_t *b_tl6 = b_tl5 + (uint32_t)1U;
  b_hd6[0U] = (uint32_t)0x1f83d9abU;
  uint32_t *b_hd7 = b_tl6;
  b_hd7[0U] = (uint32_t)0x5be0cd19U;
}

static void Hacl_Impl_SHA2_256_init(uint32_t *state)
{
  uint32_t *n1 = state + (uint32_t)136U;
  uint32_t *k1 = state;
  uint32_t *h_01 = state + (uint32_t)128U;
  Hacl_Impl_SHA2_256_constants_set_k(k1);
  Hacl_Impl_SHA2_256_assign_h0(h_01);
  n1[0U] = (uint32_t)0U;
}

static void Hacl_Impl_SHA2_256_update(uint32_t *state, uint8_t *data)
{
  uint32_t data_w[16U] = { 0U };
  Hacl_Hash_Lib_LoadStore_uint32s_from_be_bytes(data_w, data, (uint32_t)16U);
  uint32_t *hash_w = state + (uint32_t)128U;
  uint32_t *ws_w = state + (uint32_t)64U;
  uint32_t *k_w = state;
  uint32_t *counter_w = state + (uint32_t)136U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
  {
    uint32_t b = data_w[i];
    ws_w[i] = b;
  }
  for (uint32_t i = (uint32_t)16U; i < (uint32_t)64U; i = i + (uint32_t)1U)
  {
    uint32_t t16 = ws_w[i - (uint32_t)16U];
    uint32_t t15 = ws_w[i - (uint32_t)15U];
    uint32_t t7 = ws_w[i - (uint32_t)7U];
    uint32_t t2 = ws_w[i - (uint32_t)2U];
    ws_w[i] =
      ((t2 >> (uint32_t)17U | t2 << ((uint32_t)32U - (uint32_t)17U))
      ^ ((t2 >> (uint32_t)19U | t2 << ((uint32_t)32U - (uint32_t)19U)) ^ t2 >> (uint32_t)10U))
      +
        t7
        +
          ((t15 >> (uint32_t)7U | t15 << ((uint32_t)32U - (uint32_t)7U))
          ^ ((t15 >> (uint32_t)18U | t15 << ((uint32_t)32U - (uint32_t)18U)) ^ t15 >> (uint32_t)3U))
          + t16;
  }
  uint32_t hash_0[8U] = { 0U };
  memcpy(hash_0, hash_w, (uint32_t)8U * sizeof hash_w[0U]);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i = i + (uint32_t)1U)
  {
    uint32_t a = hash_0[0U];
    uint32_t b = hash_0[1U];
    uint32_t c = hash_0[2U];
    uint32_t d = hash_0[3U];
    uint32_t e = hash_0[4U];
    uint32_t f = hash_0[5U];
    uint32_t g = hash_0[6U];
    uint32_t h = hash_0[7U];
    uint32_t kt = k_w[i];
    uint32_t wst = ws_w[i];
    uint32_t
    t1 =
      h
      +
        ((e >> (uint32_t)6U | e << ((uint32_t)32U - (uint32_t)6U))
        ^
          ((e >> (uint32_t)11U | e << ((uint32_t)32U - (uint32_t)11U))
          ^ (e >> (uint32_t)25U | e << ((uint32_t)32U - (uint32_t)25U))))
      + ((e & f) ^ (~e & g))
      + kt
      + wst;
    uint32_t
    t2 =
      ((a >> (uint32_t)2U | a << ((uint32_t)32U - (uint32_t)2U))
      ^
        ((a >> (uint32_t)13U | a << ((uint32_t)32U - (uint32_t)13U))
        ^ (a >> (uint32_t)22U | a << ((uint32_t)32U - (uint32_t)22U))))
      + ((a & b) ^ ((a & c) ^ (b & c)));
    uint32_t x1 = t1 + t2;
    uint32_t x5 = d + t1;
    uint32_t *p1 = hash_0;
    uint32_t *p2 = hash_0 + (uint32_t)4U;
    p1[0U] = x1;
    p1[1U] = a;
    p1[2U] = b;
    p1[3U] = c;
    p2[0U] = x5;
    p2[1U] = e;
    p2[2U] = f;
    p2[3U] = g;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    uint32_t xi = hash_w[i];
    uint32_t yi = hash_0[i];
    hash_w[i] = xi + yi;
  }
  uint32_t c0 = counter_w[0U];
  uint32_t one1 = (uint32_t)1U;
  counter_w[0U] = c0 + one1;
}

static void Hacl_Impl_SHA2_256_update_multi(uint32_t *state, uint8_t *data, uint32_t n1)
{
  for (uint32_t i = (uint32_t)0U; i < n1; i = i + (uint32_t)1U)
  {
    uint8_t *b = data + i * (uint32_t)64U;
    Hacl_Impl_SHA2_256_update(state, b);
  }
}

static void Hacl_Impl_SHA2_256_update_last(uint32_t *state, uint8_t *data, uint32_t len)
{
  uint8_t blocks[128U] = { 0U };
  uint32_t nb;
  if (len < (uint32_t)56U)
    nb = (uint32_t)1U;
  else
    nb = (uint32_t)2U;
  uint8_t *final_blocks;
  if (len < (uint32_t)56U)
    final_blocks = blocks + (uint32_t)64U;
  else
    final_blocks = blocks;
  memcpy(final_blocks, data, len * sizeof data[0U]);
  uint32_t n1 = state[136U];
  uint8_t *padding = final_blocks + len;
  uint32_t
  pad0len = ((uint32_t)64U - (len + (uint32_t)8U + (uint32_t)1U) % (uint32_t)64U) % (uint32_t)64U;
  uint8_t *buf1 = padding;
  uint8_t *buf2 = padding + (uint32_t)1U + pad0len;
  uint64_t l_0 = (uint64_t)n1 * (uint64_t)(uint32_t)64U;
  uint64_t l_1 = (uint64_t)len;
  uint64_t encodedlen = (l_0 + l_1) * (uint64_t)(uint32_t)8U;
  buf1[0U] = (uint8_t)0x80U;
  store64_be(buf2, encodedlen);
  Hacl_Impl_SHA2_256_update_multi(state, final_blocks, nb);
}

static void Hacl_Impl_SHA2_256_finish(uint32_t *state, uint8_t *hash1)
{
  uint32_t *hash_w = state + (uint32_t)128U;
  Hacl_Hash_Lib_LoadStore_uint32s_to_be_bytes(hash1, hash_w, (uint32_t)8U);
}

static void Hacl_Impl_SHA2_256_hash(uint8_t *hash1, uint8_t *input, uint32_t len)
{
  uint32_t state[137U] = { 0U };
  uint32_t n1 = len / (uint32_t)64U;
  uint32_t r = len % (uint32_t)64U;
  uint8_t *input_blocks = input;
  uint8_t *input_last = input + n1 * (uint32_t)64U;
  Hacl_Impl_SHA2_256_init(state);
  Hacl_Impl_SHA2_256_update_multi(state, input_blocks, n1);
  Hacl_Impl_SHA2_256_update_last(state, input_last, r);
  Hacl_Impl_SHA2_256_finish(state, hash1);
}

uint32_t Hacl_SHA2_256_size_word = (uint32_t)4U;

uint32_t Hacl_SHA2_256_size_hash_w = (uint32_t)8U;

uint32_t Hacl_SHA2_256_size_block_w = (uint32_t)16U;

uint32_t Hacl_SHA2_256_size_hash = (uint32_t)32U;

uint32_t Hacl_SHA2_256_size_block = (uint32_t)64U;

uint64_t Hacl_SHA2_256_max_input_len = (uint64_t)2305843009213693952U;

uint32_t Hacl_SHA2_256_size_k_w = (uint32_t)64U;

uint32_t Hacl_SHA2_256_size_ws_w = (uint32_t)64U;

uint32_t Hacl_SHA2_256_size_whash_w = (uint32_t)8U;

uint32_t Hacl_SHA2_256_size_count_w = (uint32_t)1U;

uint32_t Hacl_SHA2_256_size_len_8 = (uint32_t)8U;

uint32_t Hacl_SHA2_256_size_state = (uint32_t)137U;

uint32_t Hacl_SHA2_256_pos_k_w = (uint32_t)0U;

uint32_t Hacl_SHA2_256_pos_ws_w = (uint32_t)64U;

uint32_t Hacl_SHA2_256_pos_whash_w = (uint32_t)128U;

uint32_t Hacl_SHA2_256_pos_count_w = (uint32_t)136U;

void Hacl_SHA2_256_init(uint32_t *state)
{
  Hacl_Impl_SHA2_256_init(state);
}

void Hacl_SHA2_256_update(uint32_t *state, uint8_t *data_8)
{
  Hacl_Impl_SHA2_256_update(state, data_8);
}

void Hacl_SHA2_256_update_multi(uint32_t *state, uint8_t *data, uint32_t n1)
{
  Hacl_Impl_SHA2_256_update_multi(state, data, n1);
}

void Hacl_SHA2_256_update_last(uint32_t *state, uint8_t *data, uint32_t len)
{
  Hacl_Impl_SHA2_256_update_last(state, data, len);
}

void Hacl_SHA2_256_finish(uint32_t *state, uint8_t *hash1)
{
  Hacl_Impl_SHA2_256_finish(state, hash1);
}

void Hacl_SHA2_256_hash(uint8_t *hash1, uint8_t *input, uint32_t len)
{
  Hacl_Impl_SHA2_256_hash(hash1, input, len);
}

