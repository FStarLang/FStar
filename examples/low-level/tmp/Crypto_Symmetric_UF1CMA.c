#include "Crypto_Symmetric_UF1CMA.h"

Crypto_Indexing_macAlg Crypto_Symmetric_UF1CMA_alg_of_id(Crypto_Indexing_id x0)
{
  return Crypto_Indexing_macAlg_of_id(x0);
}

uint32_t Crypto_Symmetric_UF1CMA_keylen(Crypto_Indexing_id i)
{
  switch (Crypto_Indexing_aeadAlg_of_id(i))
  {
    case Crypto_Indexing_aeadAlg_AES_128_GCM:
      {
        return (uint32_t )16;
        break;
      }
    case Crypto_Indexing_aeadAlg_AES_256_GCM:
      {
        return (uint32_t )16;
        break;
      }
    case Crypto_Indexing_aeadAlg_CHACHA20_POLY1305:
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

uint32_t Crypto_Symmetric_UF1CMA_skeylen(Crypto_Indexing_id i)
{
  Crypto_Indexing_aeadAlg scrut = Crypto_Indexing_aeadAlg_of_id(i);
  if (scrut == Crypto_Indexing_aeadAlg_AES_128_GCM)
    return (uint32_t )16;
  else if (scrut == Crypto_Indexing_aeadAlg_AES_256_GCM)
    return (uint32_t )16;
  else
    return (uint32_t )0;
}

bool Crypto_Symmetric_UF1CMA_skeyed(Crypto_Indexing_id i)
{
  switch (Crypto_Indexing_aeadAlg_of_id(i))
  {
    case Crypto_Indexing_aeadAlg_AES_128_GCM:
      {
        return true;
        break;
      }
    case Crypto_Indexing_aeadAlg_AES_256_GCM:
      {
        return true;
        break;
      }
    case Crypto_Indexing_aeadAlg_CHACHA20_POLY1305:
      {
        return false;
        break;
      }
    default:
      {
        printf("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        exit(253);
      }
  }
}

uint8_t
*Crypto_Symmetric_UF1CMA_get_skey(
  FStar_HyperHeap_rid rgn,
  Crypto_Indexing_id i,
  Prims_option__uint8_t_ uu____275
)
{
  if (uu____275.tag == Prims_option__uint8_t__Some)
  {
    uint8_t *k = uu____275.case_Some.v;
    return k;
  }
  else
  {
    printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
    exit(255);
  }
}

bool Crypto_Symmetric_UF1CMA_authId(K___Crypto_Indexing_id_FStar_UInt128_t i)
{
  return false && false && false;
}

void
Crypto_Symmetric_UF1CMA_log_cmp_reflexive(
  Prims_option__K___FStar_Seq_seq_FStar_Seq_seq_uint8_t_FStar_Seq_seq_uint8_t a
)
{
  return;
}

void
Crypto_Symmetric_UF1CMA_log_cmp_transitive(
  Prims_option__K___FStar_Seq_seq_FStar_Seq_seq_uint8_t_FStar_Seq_seq_uint8_t a,
  Prims_option__K___FStar_Seq_seq_FStar_Seq_seq_uint8_t_FStar_Seq_seq_uint8_t b,
  Prims_option__K___FStar_Seq_seq_FStar_Seq_seq_uint8_t_FStar_Seq_seq_uint8_t c
)
{
  return;
}

void Crypto_Symmetric_UF1CMA_log_cmp_monotonic()
{
  return;
}

void *Crypto_Symmetric_UF1CMA_ilog(FStar_HyperHeap_rid r, void *l)
{
  return (void *)(uint8_t )0;
}

FStar_HyperHeap_rid
Crypto_Symmetric_UF1CMA____State___region(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_UF1CMA_state____ projectee
)
{
  Crypto_Symmetric_UF1CMA_state____ scrut = projectee;
  FStar_HyperHeap_rid region = scrut.x00;
  Crypto_Symmetric_MAC__buffer r = scrut.x01;
  uint8_t *s = scrut.x02;
  void *log = scrut.x03;
  return region;
}

Crypto_Symmetric_MAC__buffer
Crypto_Symmetric_UF1CMA____State___r(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_UF1CMA_state____ projectee
)
{
  Crypto_Symmetric_UF1CMA_state____ scrut = projectee;
  FStar_HyperHeap_rid region = scrut.x00;
  Crypto_Symmetric_MAC__buffer r = scrut.x01;
  uint8_t *s = scrut.x02;
  void *log = scrut.x03;
  return r;
}

uint8_t
*Crypto_Symmetric_UF1CMA____State___s(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_UF1CMA_state____ projectee
)
{
  Crypto_Symmetric_UF1CMA_state____ scrut = projectee;
  FStar_HyperHeap_rid region = scrut.x00;
  Crypto_Symmetric_MAC__buffer r = scrut.x01;
  uint8_t *s = scrut.x02;
  void *log = scrut.x03;
  return s;
}

void
Crypto_Symmetric_UF1CMA____State___log(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_UF1CMA_state____ projectee
)
{
  return;
}

void Crypto_Symmetric_UF1CMA_mk_irtext(void *r)
{
  return;
}

Crypto_Symmetric_MAC__buffer
Crypto_Symmetric_UF1CMA____Acc___a(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_UF1CMA_accBuffer____ projectee
)
{
  Crypto_Symmetric_UF1CMA_accBuffer____ scrut = projectee;
  Crypto_Symmetric_MAC__buffer a = scrut.x00;
  void *l = scrut.x01;
  return a;
}

void
*Crypto_Symmetric_UF1CMA_alog(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_UF1CMA_accBuffer____ acc
)
{
  return (void *)(uint8_t )0;
}

void
Crypto_Symmetric_UF1CMA_update(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_UF1CMA_state____ st,
  Crypto_Symmetric_UF1CMA_accBuffer____ acc,
  uint8_t *w
)
{
  Crypto_Symmetric_MAC_update(i,
    Crypto_Symmetric_UF1CMA____State___r(i, st),
    Crypto_Symmetric_UF1CMA____Acc___a(i, acc),
    w);
  return;
}

void
Crypto_Symmetric_UF1CMA_mac(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_UF1CMA_state____ st,
  Crypto_Symmetric_UF1CMA_accBuffer____ acc,
  uint8_t *tag
)
{
  Crypto_Symmetric_MAC_finish(i,
    Crypto_Symmetric_UF1CMA____State___s(i, st),
    Crypto_Symmetric_UF1CMA____Acc___a(i, acc),
    tag);
  return;
}

bool
Crypto_Symmetric_UF1CMA_verify(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_UF1CMA_state____ st,
  Crypto_Symmetric_UF1CMA_accBuffer____ acc,
  uint8_t *received
)
{
  uint8_t tag[16] = { 0 };
  Crypto_Symmetric_MAC_finish(i,
    Crypto_Symmetric_UF1CMA____State___s(i, st),
    Crypto_Symmetric_UF1CMA____Acc___a(i, acc),
    tag);
  bool verified = FStar_Buffer_eqb(tag, received, (uint32_t )16);
  bool b = verified;
  return b;
}

