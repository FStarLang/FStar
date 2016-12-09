#include "Crypto_AEAD_Lemmas.h"

uint32_t Crypto_AEAD_Lemmas_u(Prims_int n)
{
  return FStar_UInt32_uint_to_t(n);
}

void
Crypto_AEAD_Lemmas_frame_pre_refines(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t nonce,
  Prims_nat len,
  uint8_t *plainb,
  uint8_t *cipherb,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2
)
{
  return;
}

void
Crypto_AEAD_Lemmas_frame_pre_refines_0(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t nonce,
  Prims_nat len,
  uint8_t *plainb,
  uint8_t *cipherb,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2
)
{
  return;
}

void
Crypto_AEAD_Lemmas_counterblocks_len(
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid rgn,
  Crypto_Symmetric_PRF_domain____ x,
  Prims_nat len,
  Prims_nat from_pos,
  void *plain,
  void *cipher
)
{
  return;
}

void
Crypto_AEAD_Lemmas_intro_refines_one_entry_no_tag(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t nonce,
  Prims_nat len,
  uint8_t *plain,
  uint8_t *cipher,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2
)
{
  return;
}

void
Crypto_AEAD_Lemmas_intro_mac_refines(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t nonce,
  uint32_t aadlen,
  uint8_t *aad,
  Prims_nat len,
  uint8_t *plain,
  uint8_t *cipher,
  FStar_HyperStack_mem h
)
{
  return;
}

void
Crypto_AEAD_Lemmas_all_above_counterblocks(
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
  return;
}

void
Crypto_AEAD_Lemmas_find_mac_counterblocks_none(
  FStar_HyperHeap_rid rgn,
  Crypto_Indexing_id i,
  FStar_UInt128_t nonce,
  void *s
)
{
  return;
}

void
Crypto_AEAD_Lemmas_find_append(
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid r,
  Crypto_Symmetric_PRF_domain____ d,
  void *s1,
  void *s2
)
{
  return;
}

void
Crypto_AEAD_Lemmas_pre_refines_to_refines(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t nonce,
  uint32_t aadlen,
  uint8_t *aad,
  Prims_nat len,
  uint8_t *plain,
  uint8_t *cipher,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h
)
{
  return;
}

void
Crypto_AEAD_Lemmas_frame_refines_one_entry(
  FStar_HyperStack_mem h,
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid mac_rgn,
  Crypto_AEAD_Invariant_entry____ e,
  void *blocks,
  FStar_HyperStack_mem h_
)
{
  return;
}

void
Crypto_AEAD_Lemmas_extend_refines(
  FStar_HyperStack_mem h,
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid mac_rgn,
  void *entries,
  void *blocks,
  Crypto_AEAD_Invariant_entry____ e,
  void *blocks_for_e,
  FStar_HyperStack_mem h_
)
{
  return;
}

void
Crypto_AEAD_Lemmas_counterblocks_emp(
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid rgn,
  Crypto_Symmetric_PRF_domain____ x,
  Prims_nat l,
  Prims_nat to_pos,
  void *plain,
  void *cipher
)
{
  return;
}

uint32_t Crypto_AEAD_Lemmas_offset(Crypto_Indexing_id i)
{
  return Crypto_Symmetric_PRF_ctr_0(i) + (uint32_t )1;
}

void
Crypto_AEAD_Lemmas_counterblocks_snoc(
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid rgn,
  Crypto_Symmetric_PRF_domain____ x,
  Prims_nat k,
  Prims_nat len,
  Prims_nat next,
  Prims_nat completed_len,
  void *plain,
  void *cipher
)
{
  return;
}

void
Crypto_AEAD_Lemmas_counterblocks_slice(
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid rgn,
  Crypto_Symmetric_PRF_domain____ x,
  Prims_nat len,
  Prims_nat from_pos,
  Prims_nat to_pos,
  void *plain,
  void *cipher
)
{
  return;
}

void
Crypto_AEAD_Lemmas_frame_counterblocks_snoc(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_state____ t,
  Crypto_Symmetric_PRF_domain____ x,
  Prims_nat k,
  Prims_nat len,
  Prims_nat completed_len,
  uint8_t *plain,
  uint8_t *cipher,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1
)
{
  return;
}

void
Crypto_AEAD_Lemmas_extending_counter_blocks(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_state____ t,
  Crypto_Symmetric_PRF_domain____ x,
  Prims_nat len,
  Prims_nat completed_len,
  uint8_t *plain,
  uint8_t *cipher,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h_init
)
{
  return;
}

