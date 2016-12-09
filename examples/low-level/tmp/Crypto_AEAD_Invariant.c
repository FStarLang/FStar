#include "Crypto_AEAD_Invariant.h"

uint32_t Crypto_AEAD_Invariant_min(uint32_t a, uint32_t b)
{
  if (a <= b)
    return a;
  else
    return b;
}

Prims_nat Crypto_AEAD_Invariant_minNat(Prims_nat a, Prims_nat b)
{
  if (Prims_op_LessThanOrEqual(a, b))
    return a;
  else
    return b;
}

uint32_t
Crypto_AEAD_Invariant_ctr(Crypto_Indexing_id uu____48, Crypto_Symmetric_PRF_domain____ x)
{
  return x.ctr;
}

FStar_UInt128_t
Crypto_AEAD_Invariant____Entry___nonce(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_entry____ projectee
)
{
  Crypto_AEAD_Invariant_entry____ scrut = projectee;
  FStar_UInt128_t nonce = scrut.x00;
  void *ad = scrut.x01;
  Prims_nat l = scrut.x02;
  void *p = scrut.x03;
  void *c = scrut.x04;
  return nonce;
}

void
*Crypto_AEAD_Invariant____Entry___ad(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_entry____ projectee
)
{
  Crypto_AEAD_Invariant_entry____ scrut = projectee;
  FStar_UInt128_t nonce = scrut.x00;
  void *ad = scrut.x01;
  Prims_nat l = scrut.x02;
  void *p = scrut.x03;
  void *c = scrut.x04;
  return ad;
}

Prims_nat
Crypto_AEAD_Invariant____Entry___l(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_entry____ projectee
)
{
  Crypto_AEAD_Invariant_entry____ scrut = projectee;
  FStar_UInt128_t nonce = scrut.x00;
  void *ad = scrut.x01;
  Prims_nat l = scrut.x02;
  void *p = scrut.x03;
  void *c = scrut.x04;
  return l;
}

void
*Crypto_AEAD_Invariant____Entry___p(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_entry____ projectee
)
{
  Crypto_AEAD_Invariant_entry____ scrut = projectee;
  FStar_UInt128_t nonce = scrut.x00;
  void *ad = scrut.x01;
  Prims_nat l = scrut.x02;
  void *p = scrut.x03;
  void *c = scrut.x04;
  return p;
}

void
*Crypto_AEAD_Invariant____Entry___c(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_entry____ projectee
)
{
  Crypto_AEAD_Invariant_entry____ scrut = projectee;
  FStar_UInt128_t nonce = scrut.x00;
  void *ad = scrut.x01;
  Prims_nat l = scrut.x02;
  void *p = scrut.x03;
  void *c = scrut.x04;
  return c;
}

bool
Crypto_AEAD_Invariant_is_entry_nonce(
  Crypto_Indexing_id i,
  FStar_UInt128_t n,
  Crypto_AEAD_Invariant_entry____ e
)
{
  return false;
}

Prims_option__Crypto_AEAD_Invariant_entry____
Crypto_AEAD_Invariant_find_entry(Crypto_Indexing_id i, FStar_UInt128_t n, void *entries)
{
  return
    (Prims_option__Crypto_AEAD_Invariant_entry____ ){
      .tag = Prims_option__Crypto_AEAD_Invariant_entry_____None,
      { .case_None = {  } }
    };
}

FStar_HyperHeap_rid
Crypto_AEAD_Invariant____State___log_region(
  Crypto_Indexing_id i,
  Crypto_Indexing_rw rw,
  Crypto_AEAD_Invariant_state_______ projectee
)
{
  Crypto_AEAD_Invariant_state_______ scrut = projectee;
  FStar_HyperHeap_rid log_region = scrut.x00;
  void *log = scrut.x01;
  Crypto_Symmetric_PRF_state____ prf = scrut.x02;
  Prims_option__uint8_t_ ak = scrut.x03;
  return log_region;
}

void
*Crypto_AEAD_Invariant____State___log(
  Crypto_Indexing_id i,
  Crypto_Indexing_rw rw,
  Crypto_AEAD_Invariant_state_______ projectee
)
{
  Crypto_AEAD_Invariant_state_______ scrut = projectee;
  FStar_HyperHeap_rid log_region = scrut.x00;
  void *log = scrut.x01;
  Crypto_Symmetric_PRF_state____ prf = scrut.x02;
  Prims_option__uint8_t_ ak = scrut.x03;
  return log;
}

Crypto_Symmetric_PRF_state____
Crypto_AEAD_Invariant____State___prf(
  Crypto_Indexing_id i,
  Crypto_Indexing_rw rw,
  Crypto_AEAD_Invariant_state_______ projectee
)
{
  Crypto_AEAD_Invariant_state_______ scrut = projectee;
  FStar_HyperHeap_rid log_region = scrut.x00;
  void *log = scrut.x01;
  Crypto_Symmetric_PRF_state____ prf = scrut.x02;
  Prims_option__uint8_t_ ak = scrut.x03;
  return prf;
}

Prims_option__uint8_t_
Crypto_AEAD_Invariant____State___ak(
  Crypto_Indexing_id i,
  Crypto_Indexing_rw rw,
  Crypto_AEAD_Invariant_state_______ projectee
)
{
  Crypto_AEAD_Invariant_state_______ scrut = projectee;
  FStar_HyperHeap_rid log_region = scrut.x00;
  void *log = scrut.x01;
  Crypto_Symmetric_PRF_state____ prf = scrut.x02;
  Prims_option__uint8_t_ ak = scrut.x03;
  return ak;
}

Prims_pos Crypto_AEAD_Invariant_maxplain(Crypto_Indexing_id i)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

bool Crypto_AEAD_Invariant_safelen(Crypto_Indexing_id i, Prims_nat l, uint32_t c)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void
*Crypto_AEAD_Invariant_counterblocks(
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid rgn,
  Crypto_Symmetric_PRF_domain____ x,
  Prims_nat l,
  Prims_nat from_pos,
  Prims_nat to_pos,
  void *plain,
  void *cipher
)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_nat Crypto_AEAD_Invariant_num_blocks_(Crypto_Indexing_id i, Prims_nat l)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_nat
Crypto_AEAD_Invariant_num_blocks(Crypto_Indexing_id i, Crypto_AEAD_Invariant_entry____ e)
{
  Crypto_AEAD_Invariant_entry____ scrut = e;
  FStar_UInt128_t nonce = scrut.x00;
  void *ad = scrut.x01;
  Prims_nat l = scrut.x02;
  void *plain = scrut.x03;
  void *cipher_tagged = scrut.x04;
  return Crypto_AEAD_Invariant_num_blocks_(i, l);
}

void
Crypto_AEAD_Invariant_refines(
  FStar_HyperStack_mem h,
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid rgn,
  void *entries,
  void *blocks
)
{
  return;
}

