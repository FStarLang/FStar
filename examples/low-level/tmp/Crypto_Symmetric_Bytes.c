#include "Crypto_Symmetric_Bytes.h"

uint8_t Crypto_Symmetric_Bytes_uint128_to_uint8(FStar_UInt128_t a)
{
  return (uint8_t )FStar_Int_Cast_uint128_to_uint64(a);
}

void Crypto_Symmetric_Bytes_print_buffer(uint8_t *s, uint32_t i, uint32_t len)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void *Crypto_Symmetric_Bytes_sel_bytes(FStar_HyperStack_mem h, uint32_t l, uint8_t *buf)
{
  return (void *)(uint8_t )0;
}

void *Crypto_Symmetric_Bytes_load_bytes(uint32_t l, uint8_t *buf)
{
  if (l == (uint32_t )0)
    return FStar_Seq_createEmpty((uint8_t )0);
  else
  {
    uint8_t b = buf[(uint32_t )0];
    void *t = Crypto_Symmetric_Bytes_load_bytes(l - (uint32_t )1, buf + (uint32_t )1);
    return FStar_SeqProperties_cons(b, t);
  }
}

void Crypto_Symmetric_Bytes_store_bytes_aux(uint32_t len, uint8_t *buf, uint32_t i, void *b)
{
  if (i < len)
  {
    buf[i] = FStar_Seq_index(b, FStar_UInt32_v(i));
    Crypto_Symmetric_Bytes_store_bytes_aux(len, buf, i + (uint32_t )1, b);
    return;
  }
  else
    return;
}

void Crypto_Symmetric_Bytes_store_bytes(uint32_t l, uint8_t *buf, void *b)
{
  Crypto_Symmetric_Bytes_store_bytes_aux(l, buf, (uint32_t )0, b);
  return;
}

void Crypto_Symmetric_Bytes_random(Prims_nat len, uint8_t *b)
{
  return;
}

void *Crypto_Symmetric_Bytes_random_bytes(uint32_t len)
{
  uint8_t buf[len];
  memset(buf, 0, len * sizeof buf[0]);
  Crypto_Symmetric_Bytes_random(FStar_UInt32_v(len), buf);
  void *b = Crypto_Symmetric_Bytes_load_bytes(len, buf);
  return b;
}

Prims_nat Crypto_Symmetric_Bytes_little_endian(void *b)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_nat Crypto_Symmetric_Bytes_big_endian(void *b)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void Crypto_Symmetric_Bytes_little_endian_null(Prims_nat len)
{
  return;
}

void Crypto_Symmetric_Bytes_little_endian_singleton(uint8_t n)
{
  return;
}

void Crypto_Symmetric_Bytes_little_endian_append(void *w1, void *w2)
{
  return;
}

void Crypto_Symmetric_Bytes_lemma_little_endian_is_bounded(void *b)
{
  return;
}

void Crypto_Symmetric_Bytes_lemma_big_endian_is_bounded(void *b)
{
  return;
}

void Crypto_Symmetric_Bytes_lemma_little_endian_lt_2_128(void *b)
{
  return;
}

uint32_t Crypto_Symmetric_Bytes_load_uint32(uint32_t len, uint8_t *buf)
{
  if (len == (uint32_t )0)
    return (uint32_t )0;
  else
  {
    uint32_t len0 = len - (uint32_t )1;
    uint32_t n = Crypto_Symmetric_Bytes_load_uint32(len0, buf + (uint32_t )1);
    uint8_t b = buf[(uint32_t )0];
    return (uint32_t )b + (uint32_t )256 * n;
  }
}

uint32_t Crypto_Symmetric_Bytes_load_big32(uint32_t len, uint8_t *buf)
{
  if (len == (uint32_t )0)
    return (uint32_t )0;
  else
  {
    uint32_t len0 = len - (uint32_t )1;
    uint32_t n = Crypto_Symmetric_Bytes_load_big32(len0, buf + (uint32_t )0);
    uint8_t b = buf[len0];
    return (uint32_t )b + (uint32_t )256 * n;
  }
}

uint64_t Crypto_Symmetric_Bytes_load_big64(uint32_t len, uint8_t *buf)
{
  if (len == (uint32_t )0)
    return (uint64_t )0;
  else
  {
    uint32_t len0 = len - (uint32_t )1;
    uint64_t n = Crypto_Symmetric_Bytes_load_big64(len0, buf + (uint32_t )0);
    uint8_t b = buf[len0];
    return (uint64_t )b + (uint64_t )256 * n;
  }
}

FStar_UInt128_t Crypto_Symmetric_Bytes_uint8_to_uint128(uint8_t a)
{
  return FStar_Int_Cast_uint64_to_uint128((uint64_t )a);
}

FStar_UInt128_t Crypto_Symmetric_Bytes_load_uint128(uint32_t len, uint8_t *buf)
{
  if (len == (uint32_t )0)
    return FStar_Int_Cast_uint64_to_uint128((uint64_t )0);
  else
  {
    FStar_UInt128_t
    n = Crypto_Symmetric_Bytes_load_uint128(len - (uint32_t )1, buf + (uint32_t )1);
    uint8_t b = buf[(uint32_t )0];
    return
      FStar_UInt128_add(Crypto_Symmetric_Bytes_uint8_to_uint128(b),
        FStar_UInt128_shift_left(n, (uint32_t )8));
  }
}

void Crypto_Symmetric_Bytes_store_uint32(uint32_t len, uint8_t *buf, uint32_t n)
{
  if (len != (uint32_t )0)
  {
    uint32_t len0 = len - (uint32_t )1;
    uint8_t b = (uint8_t )n;
    uint32_t n_ = n >> (uint32_t )8;
    uint8_t *buf_ = buf + (uint32_t )1;
    Crypto_Symmetric_Bytes_store_uint32(len0, buf_, n_);
    buf[(uint32_t )0] = b;
  }
  else
    return;
}

void Crypto_Symmetric_Bytes_store_big32(uint32_t len, uint8_t *buf, uint32_t n)
{
  if (len != (uint32_t )0)
  {
    uint32_t len0 = len - (uint32_t )1;
    uint8_t b = (uint8_t )n;
    uint32_t n_ = n >> (uint32_t )8;
    uint8_t *buf_ = buf + (uint32_t )0;
    Crypto_Symmetric_Bytes_store_big32(len0, buf_, n_);
    buf[len0] = b;
  }
  else
    return;
}

void *Crypto_Symmetric_Bytes_uint32_bytes(uint32_t len, uint32_t n)
{
  if (len == (uint32_t )0)
    return FStar_Seq_createEmpty((uint8_t )0);
  else
    return
      FStar_SeqProperties_cons((uint8_t )n,
        Crypto_Symmetric_Bytes_uint32_bytes(len - (uint32_t )1, n >> (uint32_t )8));
}

void *Crypto_Symmetric_Bytes_uint32_be(uint32_t len, uint32_t n)
{
  if (len == (uint32_t )0)
    return FStar_Seq_createEmpty((uint8_t )0);
  else
    return
      FStar_SeqProperties_snoc(Crypto_Symmetric_Bytes_uint32_be(len - (uint32_t )1,
          n >> (uint32_t )8),
        (uint8_t )n);
}

void *Crypto_Symmetric_Bytes_little_bytes(uint32_t len, Prims_nat n)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void Crypto_Symmetric_Bytes_store_uint128(uint32_t len, uint8_t *buf, FStar_UInt128_t n)
{
  if (len != (uint32_t )0)
  {
    uint32_t len0 = len - (uint32_t )1;
    uint8_t b = Crypto_Symmetric_Bytes_uint128_to_uint8(n);
    FStar_UInt128_t n_ = FStar_UInt128_shift_right(n, (uint32_t )8);
    uint8_t *buf_ = buf + (uint32_t )1;
    Crypto_Symmetric_Bytes_store_uint128(len0, buf_, n_);
    buf[(uint32_t )0] = b;
  }
  else
    return;
}

void Crypto_Symmetric_Bytes_lemma_little_endian_is_injective_0(void *b)
{
  return;
}

void
Crypto_Symmetric_Bytes_lemma_little_endian_is_injective_1(
  Prims_pos b,
  Prims_nat q,
  Prims_nat r,
  Prims_nat q_,
  Prims_nat r_
)
{
  return;
}

void Crypto_Symmetric_Bytes_lemma_little_endian_is_injective_2(void *b, Prims_pos len)
{
  return;
}

void
Crypto_Symmetric_Bytes_lemma_little_endian_is_injective_3(void *b, void *b_, Prims_pos len)
{
  return;
}

void Crypto_Symmetric_Bytes_lemma_little_endian_is_injective(void *b, void *b_, Prims_nat len)
{
  return;
}

