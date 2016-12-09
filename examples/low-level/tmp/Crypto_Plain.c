#include "Crypto_Plain.h"

void *Crypto_Plain_as_bytes(Crypto_Indexing_id i, Prims_nat l, void *p)
{
  return (void *)(uint8_t )0;
}

void *Crypto_Plain_repr(Crypto_Indexing_id i, Prims_nat l, void *p)
{
  return p;
}

void *Crypto_Plain_make(Crypto_Indexing_id i, Prims_nat l, void *b)
{
  return b;
}

void *Crypto_Plain_slice(Crypto_Indexing_id i, Prims_nat l, void *p, Prims_nat s, Prims_nat j)
{
  return FStar_Seq_slice(p, s, j);
}

uint8_t *Crypto_Plain_as_buffer(Crypto_Indexing_id i, Prims_nat l, uint8_t *pb)
{
  return (uint8_t *)(uint8_t )0;
}

uint8_t *Crypto_Plain_unsafe_hide_buffer(Crypto_Indexing_id i, Prims_nat l, uint8_t *b)
{
  return b;
}

uint8_t *Crypto_Plain_hide_buffer(Crypto_Indexing_id i, Prims_nat l, uint8_t *b)
{
  return (uint8_t *)(uint8_t )0;
}

void Crypto_Plain_as_buffer_injective(Crypto_Indexing_id i, Prims_nat l, uint8_t *p)
{
  return;
}

void
*Crypto_Plain_sel_plain(FStar_HyperStack_mem h, Crypto_Indexing_id i, uint32_t l, uint8_t *buf)
{
  return (void *)(uint8_t )0;
}

uint8_t *Crypto_Plain_bufferRepr(Crypto_Indexing_id i, Prims_nat l, uint8_t *b)
{
  return b;
}

uint8_t
*Crypto_Plain_sub(Crypto_Indexing_id id, Prims_nat l, uint8_t *b, uint32_t i, uint32_t len)
{
  return b + i;
}

void *Crypto_Plain_load(Crypto_Indexing_id i, uint32_t l, uint8_t *buf)
{
  return Crypto_Symmetric_Bytes_load_bytes(l, buf);
}

void Crypto_Plain_store(Crypto_Indexing_id i, uint32_t l, uint8_t *buf, void *b)
{
  Crypto_Symmetric_Bytes_store_bytes(l, buf, b);
  return;
}

