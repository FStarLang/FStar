#include "Crypto_Symmetric_AES128.h"

Prims_nat Crypto_Symmetric_AES128_v(uint32_t x)
{
  return FStar_UInt32_v(x);
}

uint32_t Crypto_Symmetric_AES128_nb = (uint32_t )4;

uint32_t Crypto_Symmetric_AES128_nk = (uint32_t )4;

uint32_t Crypto_Symmetric_AES128_nr = (uint32_t )10;

uint32_t Crypto_Symmetric_AES128_blocklen = (uint32_t )16;

uint32_t Crypto_Symmetric_AES128_keylen = (uint32_t )16;

uint32_t Crypto_Symmetric_AES128_xkeylen = (uint32_t )176;

uint8_t Crypto_Symmetric_AES128_xtime(uint8_t b)
{
  return b << (uint32_t )1 ^ (b >> (uint32_t )7 & (uint8_t )1) * (uint8_t )0x1b;
}

uint8_t Crypto_Symmetric_AES128_multiply(uint8_t a, uint8_t b)
{
  return
    a
    * (b & (uint8_t )1)
    ^
      Crypto_Symmetric_AES128_xtime(a)
      * (b >> (uint32_t )1 & (uint8_t )1)
      ^
        Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(a))
        * (b >> (uint32_t )2 & (uint8_t )1)
        ^
          Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(a)))
          * (b >> (uint32_t )3 & (uint8_t )1)
          ^
            Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(a))))
            * (b >> (uint32_t )4 & (uint8_t )1)
            ^
              Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(a)))))
              * (b >> (uint32_t )5 & (uint8_t )1)
              ^
                Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(a))))))
                * (b >> (uint32_t )6 & (uint8_t )1)
                ^
                  Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(Crypto_Symmetric_AES128_xtime(a)))))))
                  * (b >> (uint32_t )7 & (uint8_t )1);
}

void Crypto_Symmetric_AES128_mk_sbox(uint8_t *sbox)
{
  return;
}

void Crypto_Symmetric_AES128_mk_inv_sbox(uint8_t *sbox)
{
  return;
}

uint8_t Crypto_Symmetric_AES128_access_aux(uint8_t *sbox, uint8_t i, uint32_t ctr, uint8_t tmp)
{
  if (ctr == (uint32_t )256)
    return tmp;
  else
  {
    uint8_t mask = FStar_UInt8_eq_mask(i, (uint8_t )ctr);
    uint8_t _0_74 = sbox[ctr];
    uint8_t _0_75 = mask & _0_74;
    uint8_t tmp0 = tmp | _0_75;
    return Crypto_Symmetric_AES128_access_aux(sbox, i, ctr + (uint32_t )1, tmp0);
  }
}

uint8_t Crypto_Symmetric_AES128_access(uint8_t *sbox, uint8_t i)
{
  return sbox[(uint32_t )i];
}

void Crypto_Symmetric_AES128_subBytes_aux_sbox(uint8_t *state, uint8_t *sbox, uint32_t ctr)
{
  if (ctr != (uint32_t )16)
  {
    uint8_t si = state[ctr];
    uint8_t si_ = Crypto_Symmetric_AES128_access(sbox, si);
    state[ctr] = si_;
    Crypto_Symmetric_AES128_subBytes_aux_sbox(state, sbox, ctr + (uint32_t )1);
    return;
  }
  else
    return;
}

void Crypto_Symmetric_AES128_subBytes_sbox(uint8_t *state, uint8_t *sbox)
{
  Crypto_Symmetric_AES128_subBytes_aux_sbox(state, sbox, (uint32_t )0);
  return;
}

void Crypto_Symmetric_AES128_shiftRows(uint8_t *state)
{
  uint32_t i = (uint32_t )1;
  uint8_t tmp0 = state[i];
  uint8_t _0_76 = state[i + (uint32_t )4];
  state[i] = _0_76;
  uint8_t _0_77 = state[i + (uint32_t )8];
  state[i + (uint32_t )4] = _0_77;
  uint8_t _0_78 = state[i + (uint32_t )12];
  state[i + (uint32_t )8] = _0_78;
  state[i + (uint32_t )12] = tmp0;
  uint32_t i0 = (uint32_t )2;
  uint8_t tmp1 = state[i0];
  uint8_t _0_79 = state[i0 + (uint32_t )8];
  state[i0] = _0_79;
  state[i0 + (uint32_t )8] = tmp1;
  uint8_t tmp2 = state[i0 + (uint32_t )4];
  uint8_t _0_80 = state[i0 + (uint32_t )12];
  state[i0 + (uint32_t )4] = _0_80;
  state[i0 + (uint32_t )12] = tmp2;
  uint32_t i1 = (uint32_t )3;
  uint8_t tmp = state[i1];
  uint8_t _0_81 = state[i1 + (uint32_t )12];
  state[i1] = _0_81;
  uint8_t _0_82 = state[i1 + (uint32_t )8];
  state[i1 + (uint32_t )12] = _0_82;
  uint8_t _0_83 = state[i1 + (uint32_t )4];
  state[i1 + (uint32_t )8] = _0_83;
  state[i1 + (uint32_t )4] = tmp;
}

void Crypto_Symmetric_AES128_mixColumns_(uint8_t *state, uint32_t c)
{
  uint8_t *s = state + (uint32_t )4 * c;
  uint8_t s0 = s[(uint32_t )0];
  uint8_t s1 = s[(uint32_t )1];
  uint8_t s2 = s[(uint32_t )2];
  uint8_t s3 = s[(uint32_t )3];
  s[(uint32_t )0] =
    Crypto_Symmetric_AES128_multiply((uint8_t )0x2,
      s0)
    ^ Crypto_Symmetric_AES128_multiply((uint8_t )0x3, s1) ^ s2 ^ s3;
  s[(uint32_t )1] =
    Crypto_Symmetric_AES128_multiply((uint8_t )0x2,
      s1)
    ^ Crypto_Symmetric_AES128_multiply((uint8_t )0x3, s2) ^ s3 ^ s0;
  s[(uint32_t )2] =
    Crypto_Symmetric_AES128_multiply((uint8_t )0x2,
      s2)
    ^ Crypto_Symmetric_AES128_multiply((uint8_t )0x3, s3) ^ s0 ^ s1;
  s[(uint32_t )3] =
    Crypto_Symmetric_AES128_multiply((uint8_t )0x2,
      s3)
    ^ Crypto_Symmetric_AES128_multiply((uint8_t )0x3, s0) ^ s1 ^ s2;
}

void Crypto_Symmetric_AES128_mixColumns(uint8_t *state)
{
  Crypto_Symmetric_AES128_mixColumns_(state, (uint32_t )0);
  Crypto_Symmetric_AES128_mixColumns_(state, (uint32_t )1);
  Crypto_Symmetric_AES128_mixColumns_(state, (uint32_t )2);
  Crypto_Symmetric_AES128_mixColumns_(state, (uint32_t )3);
  return;
}

void
Crypto_Symmetric_AES128_addRoundKey_(uint8_t *state, uint8_t *w, uint32_t round, uint32_t c)
{
  uint8_t *target = state + (uint32_t )4 * c;
  uint8_t *subkey = w + Crypto_Symmetric_AES128_blocklen * round + (uint32_t )4 * c;
  uint8_t _0_85 = target[(uint32_t )0];
  uint8_t _0_84 = subkey[(uint32_t )0];
  uint8_t _0_86 = _0_85 ^ _0_84;
  target[(uint32_t )0] = _0_86;
  uint8_t _0_88 = target[(uint32_t )1];
  uint8_t _0_87 = subkey[(uint32_t )1];
  uint8_t _0_89 = _0_88 ^ _0_87;
  target[(uint32_t )1] = _0_89;
  uint8_t _0_91 = target[(uint32_t )2];
  uint8_t _0_90 = subkey[(uint32_t )2];
  uint8_t _0_92 = _0_91 ^ _0_90;
  target[(uint32_t )2] = _0_92;
  uint8_t _0_94 = target[(uint32_t )3];
  uint8_t _0_93 = subkey[(uint32_t )3];
  uint8_t _0_95 = _0_94 ^ _0_93;
  target[(uint32_t )3] = _0_95;
}

void Crypto_Symmetric_AES128_addRoundKey(uint8_t *state, uint8_t *w, uint32_t round)
{
  Crypto_Symmetric_AES128_addRoundKey_(state, w, round, (uint32_t )0);
  Crypto_Symmetric_AES128_addRoundKey_(state, w, round, (uint32_t )1);
  Crypto_Symmetric_AES128_addRoundKey_(state, w, round, (uint32_t )2);
  Crypto_Symmetric_AES128_addRoundKey_(state, w, round, (uint32_t )3);
  return;
}

void
Crypto_Symmetric_AES128_cipher_loop(uint8_t *state, uint8_t *w, uint8_t *sbox, uint32_t round)
{
  if (round != (uint32_t )10)
  {
    Crypto_Symmetric_AES128_subBytes_sbox(state, sbox);
    Crypto_Symmetric_AES128_shiftRows(state);
    Crypto_Symmetric_AES128_mixColumns(state);
    Crypto_Symmetric_AES128_addRoundKey(state, w, round);
    Crypto_Symmetric_AES128_cipher_loop(state, w, sbox, round + (uint32_t )1);
    return;
  }
  else
    return;
}

void Crypto_Symmetric_AES128_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox)
{
  Intrinsics_aes128_enc(out, input);
  return;
}

void Crypto_Symmetric_AES128_rotWord(uint8_t *word)
{
  uint8_t w0 = word[(uint32_t )0];
  uint8_t w1 = word[(uint32_t )1];
  uint8_t w2 = word[(uint32_t )2];
  uint8_t w3 = word[(uint32_t )3];
  word[(uint32_t )0] = w1;
  word[(uint32_t )1] = w2;
  word[(uint32_t )2] = w3;
  word[(uint32_t )3] = w0;
}

void Crypto_Symmetric_AES128_subWord(uint8_t *word, uint8_t *sbox)
{
  uint8_t _0_96 = word[(uint32_t )0];
  uint8_t _0_97 = Crypto_Symmetric_AES128_access(sbox, _0_96);
  word[(uint32_t )0] = _0_97;
  uint8_t _0_98 = word[(uint32_t )1];
  uint8_t _0_99 = Crypto_Symmetric_AES128_access(sbox, _0_98);
  word[(uint32_t )1] = _0_99;
  uint8_t _0_100 = word[(uint32_t )2];
  uint8_t _0_101 = Crypto_Symmetric_AES128_access(sbox, _0_100);
  word[(uint32_t )2] = _0_101;
  uint8_t _0_102 = word[(uint32_t )3];
  uint8_t _0_103 = Crypto_Symmetric_AES128_access(sbox, _0_102);
  word[(uint32_t )3] = _0_103;
}

uint8_t Crypto_Symmetric_AES128_rcon(uint32_t i, uint8_t tmp)
{
  if (i == (uint32_t )1)
    return tmp;
  else
    return
      Crypto_Symmetric_AES128_rcon(i - (uint32_t )1,
        Crypto_Symmetric_AES128_multiply((uint8_t )0x2, tmp));
}

void
Crypto_Symmetric_AES128_keyExpansion_aux_0(
  uint8_t *w,
  uint8_t *temp,
  uint8_t *sbox,
  uint32_t j
)
{
  memcpy(temp, w + (uint32_t )4 * j - (uint32_t )4, (uint32_t )4 * sizeof w[0]);
  if (j % (uint32_t )4 == (uint32_t )0)
  {
    Crypto_Symmetric_AES128_rotWord(temp);
    Crypto_Symmetric_AES128_subWord(temp, sbox);
    uint8_t t0 = temp[(uint32_t )0];
    uint8_t rc = Crypto_Symmetric_AES128_rcon(j / (uint32_t )4, (uint8_t )1);
    uint8_t z = t0 ^ rc;
    temp[(uint32_t )0] = z;
  }
  else if (j % (uint32_t )4 == (uint32_t )4)
  {
    Crypto_Symmetric_AES128_subWord(temp, sbox);
    return;
  }
  else
    return;
}

void
Crypto_Symmetric_AES128_keyExpansion_aux_1(
  uint8_t *w,
  uint8_t *temp,
  uint8_t *sbox,
  uint32_t j
)
{
  uint32_t i = (uint32_t )4 * j;
  uint8_t w0 = w[i + (uint32_t )0 - Crypto_Symmetric_AES128_keylen];
  uint8_t w1 = w[i + (uint32_t )1 - Crypto_Symmetric_AES128_keylen];
  uint8_t w2 = w[i + (uint32_t )2 - Crypto_Symmetric_AES128_keylen];
  uint8_t w3 = w[i + (uint32_t )3 - Crypto_Symmetric_AES128_keylen];
  uint8_t t0 = temp[(uint32_t )0];
  uint8_t t1 = temp[(uint32_t )1];
  uint8_t t2 = temp[(uint32_t )2];
  uint8_t t3 = temp[(uint32_t )3];
  w[i + (uint32_t )0] = t0 ^ w0;
  w[i + (uint32_t )1] = t1 ^ w1;
  w[i + (uint32_t )2] = t2 ^ w2;
  w[i + (uint32_t )3] = t3 ^ w3;
}

void
Crypto_Symmetric_AES128_keyExpansion_aux(uint8_t *w, uint8_t *temp, uint8_t *sbox, uint32_t j)
{
  if (j < Crypto_Symmetric_AES128_xkeylen / (uint32_t )4)
  {
    Crypto_Symmetric_AES128_keyExpansion_aux_0(w, temp, sbox, j);
    Crypto_Symmetric_AES128_keyExpansion_aux_1(w, temp, sbox, j);
    Crypto_Symmetric_AES128_keyExpansion_aux(w, temp, sbox, j + (uint32_t )1);
    return;
  }
  else
    return;
}

void Crypto_Symmetric_AES128_keyExpansion(uint8_t *key, uint8_t *w, uint8_t *sbox)
{
  Intrinsics_aes128_load(key);
  return;
}

void Crypto_Symmetric_AES128_invSubBytes_aux_sbox(uint8_t *state, uint8_t *sbox, uint32_t ctr)
{
  if (ctr == (uint32_t )16)
    return;
  else
  {
    uint8_t si = state[ctr];
    uint8_t si_ = Crypto_Symmetric_AES128_access(sbox, si);
    state[ctr] = si_;
    Crypto_Symmetric_AES128_invSubBytes_aux_sbox(state, sbox, ctr + (uint32_t )1);
    return;
  }
}

void Crypto_Symmetric_AES128_invSubBytes_sbox(uint8_t *state, uint8_t *sbox)
{
  Crypto_Symmetric_AES128_invSubBytes_aux_sbox(state, sbox, (uint32_t )0);
  return;
}

void Crypto_Symmetric_AES128_invShiftRows(uint8_t *state)
{
  uint32_t i = (uint32_t )3;
  uint8_t tmp0 = state[i];
  uint8_t _0_104 = state[i + (uint32_t )4];
  state[i] = _0_104;
  uint8_t _0_105 = state[i + (uint32_t )8];
  state[i + (uint32_t )4] = _0_105;
  uint8_t _0_106 = state[i + (uint32_t )12];
  state[i + (uint32_t )8] = _0_106;
  state[i + (uint32_t )12] = tmp0;
  uint32_t i0 = (uint32_t )2;
  uint8_t tmp1 = state[i0];
  uint8_t _0_107 = state[i0 + (uint32_t )8];
  state[i0] = _0_107;
  state[i0 + (uint32_t )8] = tmp1;
  uint8_t tmp2 = state[i0 + (uint32_t )4];
  uint8_t _0_108 = state[i0 + (uint32_t )12];
  state[i0 + (uint32_t )4] = _0_108;
  state[i0 + (uint32_t )12] = tmp2;
  uint32_t i1 = (uint32_t )1;
  uint8_t tmp = state[i1];
  uint8_t _0_109 = state[i1 + (uint32_t )12];
  state[i1] = _0_109;
  uint8_t _0_110 = state[i1 + (uint32_t )8];
  state[i1 + (uint32_t )12] = _0_110;
  uint8_t _0_111 = state[i1 + (uint32_t )4];
  state[i1 + (uint32_t )8] = _0_111;
  state[i1 + (uint32_t )4] = tmp;
}

void Crypto_Symmetric_AES128_invMixColumns_(uint8_t *state, uint32_t c)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void Crypto_Symmetric_AES128_invMixColumns(uint8_t *state)
{
  Crypto_Symmetric_AES128_invMixColumns_(state, (uint32_t )0);
  Crypto_Symmetric_AES128_invMixColumns_(state, (uint32_t )1);
  Crypto_Symmetric_AES128_invMixColumns_(state, (uint32_t )2);
  Crypto_Symmetric_AES128_invMixColumns_(state, (uint32_t )3);
  return;
}

void
Crypto_Symmetric_AES128_inv_cipher_loop(
  uint8_t *state,
  uint8_t *w,
  uint8_t *sbox,
  uint32_t round
)
{
  if (round != (uint32_t )0)
  {
    Crypto_Symmetric_AES128_invShiftRows(state);
    Crypto_Symmetric_AES128_invSubBytes_sbox(state, sbox);
    Crypto_Symmetric_AES128_addRoundKey(state, w, round);
    Crypto_Symmetric_AES128_invMixColumns(state);
    Crypto_Symmetric_AES128_inv_cipher_loop(state, w, sbox, round - (uint32_t )1);
    return;
  }
  else
    return;
}

void
Crypto_Symmetric_AES128_inv_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox)
{
  Intrinsics_aes128_dec(out, input);
  return;
}

