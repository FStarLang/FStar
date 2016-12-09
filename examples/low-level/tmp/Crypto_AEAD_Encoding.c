#include "Crypto_AEAD_Encoding.h"

Crypto_Indexing_cipherAlg Crypto_AEAD_Encoding_alg(Crypto_Indexing_id i)
{
  return Crypto_Indexing_cipherAlg_of_id(i);
}

uint32_t Crypto_AEAD_Encoding_txtmax = (uint32_t )16485;

uint32_t Crypto_AEAD_Encoding_aadmax = (uint32_t )2000;

void *Crypto_AEAD_Encoding_pad_0(void *b, Prims_nat l)
{
  return FStar_Seq_append(b, FStar_Seq_create(l, (uint8_t )0));
}

void *Crypto_AEAD_Encoding_encode_bytes(void *txt)
{
  return (void *)(uint8_t )0;
}

void Crypto_AEAD_Encoding_lemma_encode_length(void *txt)
{
  return;
}

Prims_nat Crypto_AEAD_Encoding_p_1305;

void Crypto_AEAD_Encoding_lemma_pad_0_injective(void *b0, void *b1, Prims_nat l)
{
  return;
}

void Crypto_AEAD_Encoding_pad_16(uint8_t *b, uint32_t len)
{
  Buffer_Utils_memset(b + len, (uint8_t )0, (uint32_t )16 - len);
  return;
}

void
Crypto_AEAD_Encoding_add_bytes(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_UF1CMA_state____ st,
  Crypto_Symmetric_UF1CMA_accBuffer____ a,
  uint32_t len,
  uint8_t *txt
)
{
  uint8_t w[16];
  if (len != (uint32_t )0)
    if (len < (uint32_t )16)
    {
      memset(w, 0, (uint32_t )16 * sizeof w[0]);
      memcpy(w, txt, len * sizeof txt[0]);
      Crypto_AEAD_Encoding_pad_16(w, len);
      Crypto_Symmetric_UF1CMA_update(i, st, a, w);
    }
    else
    {
      uint8_t *w = txt + (uint32_t )0;
      Crypto_Symmetric_UF1CMA_update(i, st, a, w);
      Crypto_AEAD_Encoding_add_bytes(i, st, a, len - (uint32_t )16, txt + (uint32_t )16);
    }
}

void
*Crypto_AEAD_Encoding_encode_both(
  Crypto_Indexing_id i,
  uint32_t aadlen,
  void *aad,
  uint32_t txtlen,
  void *cipher
)
{
  return (void *)(uint8_t )0;
}

void
Crypto_AEAD_Encoding_lemma_encode_both_inj(
  Crypto_Indexing_id i,
  uint32_t al0,
  uint32_t pl0,
  uint32_t al1,
  uint32_t pl1,
  void *a0,
  void *p0,
  void *a1,
  void *p1
)
{
  return;
}

