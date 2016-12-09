#include "Crypto_Symmetric_Cipher.h"

uint32_t Crypto_Symmetric_Cipher_keylen(Crypto_Indexing_cipherAlg uu___41_4)
{
  switch (uu___41_4)
  {
    case Crypto_Indexing_cipherAlg_AES128:
      {
        return (uint32_t )16;
        break;
      }
    case Crypto_Indexing_cipherAlg_AES256:
      {
        return (uint32_t )32;
        break;
      }
    case Crypto_Indexing_cipherAlg_CHACHA20:
      {
        return (uint32_t )32;
        break;
      }
    default:
      {
        printf("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        exit(253);
      }
  }
}

uint32_t Crypto_Symmetric_Cipher_blocklen(Crypto_Indexing_cipherAlg uu___42_23)
{
  switch (uu___42_23)
  {
    case Crypto_Indexing_cipherAlg_AES128:
      {
        return (uint32_t )16;
        break;
      }
    case Crypto_Indexing_cipherAlg_AES256:
      {
        return (uint32_t )16;
        break;
      }
    case Crypto_Indexing_cipherAlg_CHACHA20:
      {
        return (uint32_t )64;
        break;
      }
    default:
      {
        printf("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        exit(253);
      }
  }
}

uint32_t Crypto_Symmetric_Cipher_ivlen(Crypto_Indexing_cipherAlg a)
{
  return (uint32_t )12;
}

uint32_t Crypto_Symmetric_Cipher_statelen(Crypto_Indexing_cipherAlg uu___43_51)
{
  switch (uu___43_51)
  {
    case Crypto_Indexing_cipherAlg_AES128:
      {
        return (uint32_t )432;
        break;
      }
    case Crypto_Indexing_cipherAlg_AES256:
      {
        return (uint32_t )496;
        break;
      }
    case Crypto_Indexing_cipherAlg_CHACHA20:
      {
        return (uint32_t )64;
        break;
      }
    default:
      {
        printf("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        exit(253);
      }
  }
}

void Crypto_Symmetric_Cipher_init(Crypto_Indexing_cipherAlg a, uint8_t *k, uint8_t *s)
{
  switch (a)
  {
    case Crypto_Indexing_cipherAlg_CHACHA20:
      {
        uint32_t *ctx = Crypto_Symmetric_Cipher_p8_to_p32(s);
        Crypto_Symmetric_Chacha20_chacha_keysetup(ctx, k);
        return;
        break;
      }
    case Crypto_Indexing_cipherAlg_AES128:
      {
        uint8_t *sbox = s + (uint32_t )0;
        uint8_t *w = s + (uint32_t )256;
        Crypto_Symmetric_AES128_mk_sbox(sbox);
        Crypto_Symmetric_AES128_keyExpansion(k, w, sbox);
        return;
        break;
      }
    case Crypto_Indexing_cipherAlg_AES256:
      {
        uint8_t *sbox = s + (uint32_t )0;
        uint8_t *w = s + (uint32_t )256;
        Crypto_Symmetric_AES_mk_sbox(sbox);
        Crypto_Symmetric_AES_keyExpansion(k, w, sbox);
        return;
        break;
      }
    default:
      {
        printf("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        exit(253);
      }
  }
}

void Crypto_Symmetric_Cipher_aes_store_counter(uint8_t *b, uint32_t x)
{
  uint8_t b0 = (uint8_t )(x & (uint32_t )255);
  uint8_t b1 = (uint8_t )(x >> (uint32_t )8 & (uint32_t )255);
  uint8_t b2 = (uint8_t )(x >> (uint32_t )16 & (uint32_t )255);
  uint8_t b3 = (uint8_t )(x >> (uint32_t )24 & (uint32_t )255);
  b[(uint32_t )15] = b0;
  b[(uint32_t )14] = b1;
  b[(uint32_t )13] = b2;
  b[(uint32_t )12] = b3;
}

void
Crypto_Symmetric_Cipher_compute(
  Crypto_Indexing_cipherAlg a,
  uint8_t *output,
  uint8_t *st,
  FStar_UInt128_t n,
  uint32_t counter,
  uint32_t len
)
{
  switch (a)
  {
    case Crypto_Indexing_cipherAlg_CHACHA20:
      {
        uint32_t *ctx = Crypto_Symmetric_Cipher_p8_to_p32(st);
        if (counter <= (uint32_t )1)
        {
          uint8_t nbuf[12] = { 0 };
          Crypto_Symmetric_Bytes_store_uint128((uint32_t )12, nbuf, n);
          Crypto_Symmetric_Chacha20_chacha_ietf_ivsetup(ctx, nbuf, counter);
        }
        Crypto_Symmetric_Chacha20_chacha_encrypt_bytes(ctx, output, output, len);
        break;
      }
    case Crypto_Indexing_cipherAlg_AES128:
      {
        uint8_t *sbox = st + (uint32_t )0;
        uint8_t *w = st + (uint32_t )256;
        uint8_t ctr_block[16] = { 0 };
        Crypto_Symmetric_Bytes_store_uint128((uint32_t )12, ctr_block + (uint32_t )0, n);
        Crypto_Symmetric_Cipher_aes_store_counter(ctr_block, counter);
        uint8_t output_block[16] = { 0 };
        Crypto_Symmetric_AES128_cipher(output_block, ctr_block, w, sbox);
        memcpy(output, output_block, len * sizeof output_block[0]);
        break;
      }
    case Crypto_Indexing_cipherAlg_AES256:
      {
        uint8_t *sbox = st + (uint32_t )0;
        uint8_t *w = st + (uint32_t )256;
        uint8_t ctr_block[16] = { 0 };
        Crypto_Symmetric_Bytes_store_uint128((uint32_t )12, ctr_block + (uint32_t )0, n);
        Crypto_Symmetric_Cipher_aes_store_counter(ctr_block, counter);
        uint8_t output_block[16] = { 0 };
        Crypto_Symmetric_AES_cipher(output_block, ctr_block, w, sbox);
        memcpy(output, output_block, len * sizeof output_block[0]);
        break;
      }
    default:
      {
        printf("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        exit(253);
      }
  }
}

