#include "Crypto_AEAD.h"

uint32_t Crypto_AEAD_ctr(Crypto_Indexing_id uu____15, Crypto_Symmetric_PRF_domain____ x)
{
  return x.ctr;
}

void
Crypto_AEAD_mac_wrapper(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_UF1CMA_state____ st,
  Crypto_Symmetric_UF1CMA_accBuffer____ acc,
  uint8_t *tag
)
{
  Crypto_Symmetric_UF1CMA_mac(i, st, acc, tag);
  return;
}

void Crypto_AEAD_lemma_xor_bounded(Prims_nat n, FStar_UInt128_t x, FStar_UInt128_t y)
{
  return;
}

FStar_UInt128_t Crypto_AEAD_aeIV(Crypto_Indexing_id i, uint64_t seqn, FStar_UInt128_t staticIV)
{
  return FStar_UInt128_logxor(FStar_Int_Cast_uint64_to_uint128(seqn), staticIV);
}

Crypto_AEAD_Invariant_state_______
Crypto_AEAD_genReader(Crypto_Indexing_id i, Crypto_AEAD_Invariant_state_______ st)
{
  return
    (Crypto_AEAD_Invariant_state_______ ){
      .x00 = Crypto_AEAD_Invariant____State___log_region(i, Crypto_Indexing_rw_Writer, st),
      .x01 = Crypto_AEAD_Invariant____State___log(i, Crypto_Indexing_rw_Writer, st),
      .x02 = Crypto_AEAD_Invariant____State___prf(i, Crypto_Indexing_rw_Writer, st),
      .x03 = Crypto_AEAD_Invariant____State___ak(i, Crypto_Indexing_rw_Writer, st)
    };
}

uint8_t *Crypto_AEAD_leak(Crypto_Indexing_id i, Crypto_AEAD_Invariant_state_______ st)
{
  return
    Crypto_Symmetric_PRF_leak(i,
      Crypto_AEAD_Invariant____State___prf(i, Crypto_Indexing_rw_Writer, st));
}

void
Crypto_AEAD_counter_enxor(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_state____ t,
  Crypto_Symmetric_PRF_domain____ x,
  uint32_t len,
  uint32_t remaining_len,
  uint8_t *plain,
  uint8_t *cipher,
  FStar_HyperStack_mem h_init
)
{
  uint32_t completed_len = len - remaining_len;
  if (remaining_len != (uint32_t )0)
  {
    uint32_t starting_pos = len - remaining_len;
    uint32_t l = Crypto_AEAD_Invariant_min(remaining_len, Crypto_Symmetric_PRF_blocklen(i));
    uint8_t *cipher_hd = cipher + starting_pos;
    uint8_t *plain_hd = Crypto_Plain_sub(i, FStar_UInt32_v(len), plain, starting_pos, l);
    Crypto_Symmetric_PRF_prf_enxor(i, t, x, l, cipher_hd, plain_hd);
    Crypto_Symmetric_PRF_domain____ y = Crypto_Symmetric_PRF_incr(i, x);
    Crypto_AEAD_counter_enxor(i, t, y, len, remaining_len - l, plain, cipher, h_init);
    return;
  }
  else
    return;
}

Crypto_Symmetric_PRF_state____
Crypto_AEAD_prf_state(
  Crypto_Indexing_id i,
  Crypto_Indexing_rw rw,
  Crypto_AEAD_Invariant_state_______ e
)
{
  return Crypto_AEAD_Invariant____State___prf(i, rw, e);
}

void
Crypto_AEAD_lemma_frame_find_mac(
  Crypto_Indexing_id i,
  Prims_nat l,
  Crypto_Symmetric_PRF_state____ st,
  Crypto_Symmetric_PRF_domain____ x,
  uint8_t *b,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1
)
{
  return;
}

void
Crypto_AEAD_heap_modifies_fresh_empty_0(
  FStar_Heap_heap h0,
  FStar_Heap_heap h1,
  FStar_Heap_heap h2,
  FStar_Heap_ref__Prims_nat x
)
{
  return;
}

void
Crypto_AEAD_modifies_fresh_empty_0(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2,
  FStar_HyperHeap_rid r,
  void *x
)
{
  return;
}

void
Crypto_AEAD_modifies_fresh_empty(
  Crypto_Indexing_id i,
  FStar_UInt128_t n,
  FStar_HyperHeap_rid r,
  Crypto_Symmetric_UF1CMA_state____ m,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2
)
{
  return;
}

void
Crypto_AEAD_extend_refines_aux(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t nonce,
  uint32_t aadlen,
  uint8_t *aad,
  Prims_nat len,
  uint8_t *plain,
  uint8_t *cipher,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1
)
{
  return;
}

void
Crypto_AEAD_frame_refines(
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid mac_rgn,
  void *entries,
  void *blocks,
  FStar_HyperStack_mem h,
  FStar_HyperStack_mem h_
)
{
  return;
}

void
Crypto_AEAD_refines_to_inv(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t nonce,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t len,
  uint8_t *plain,
  uint8_t *cipher
)
{
  return;
}

void
Crypto_AEAD_finish_after_mac(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h3,
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t n,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t plainlen,
  uint8_t *plain,
  uint8_t *cipher_tagged,
  Crypto_Symmetric_UF1CMA_state____ ak,
  Crypto_Symmetric_UF1CMA_accBuffer____ acc,
  uint8_t *tag
)
{
  return;
}

void
Crypto_AEAD_modifies_push_pop(
  FStar_HyperStack_mem h,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h5,
  bool (*r)(FStar_HyperHeap_rid x0)
)
{
  return;
}

void
Crypto_AEAD_frame_refines_(
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid mac_rgn,
  void *entries,
  void *blocks,
  FStar_HyperStack_mem h,
  FStar_HyperStack_mem h_
)
{
  return;
}

void
Crypto_AEAD_frame_myinv_push(
  Crypto_Indexing_id i,
  Crypto_Indexing_rw rw,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_HyperStack_mem h,
  FStar_HyperStack_mem h1
)
{
  return;
}

void
Crypto_AEAD_encrypt_ensures_push_pop(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t n,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t plainlen,
  uint8_t *plain,
  uint8_t *cipher_tagged,
  FStar_HyperStack_mem h,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h5
)
{
  return;
}

void
Crypto_AEAD_encrypt(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t n,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t plainlen,
  uint8_t *plain,
  uint8_t *cipher_tagged
)
{
  FStar_HyperStack_mem h0 = (void *)(uint8_t )0;
  Crypto_Symmetric_PRF_domain____ x = { .iv = n, .ctr = Crypto_Symmetric_PRF_ctr_0(i) };
  FStar_Buffer_recall(Crypto_Symmetric_PRF____State___key(i,
      Crypto_AEAD_Invariant____State___prf(i, Crypto_Indexing_rw_Writer, st)));
  FStar_ST_recall_region(Crypto_Symmetric_PRF____State___mac_rgn(i,
      Crypto_AEAD_Invariant____State___prf(i, Crypto_Indexing_rw_Writer, st)));
  K___Crypto_Indexing_id_FStar_UInt128_t macId = { .fst = i, .snd = x.iv };
  uint8_t *keyBuffer = calloc(Crypto_Symmetric_UF1CMA_keylen(i), sizeof (uint8_t ));
  Crypto_Symmetric_PRF_getBlock(i,
    Crypto_AEAD_Invariant____State___prf(i, Crypto_Indexing_rw_Writer, st),
    x,
    Crypto_Symmetric_UF1CMA_keylen(i),
    keyBuffer);
  Crypto_Symmetric_MAC__buffer r;
  switch (Crypto_Symmetric_MAC_alg(macId))
  {
    case Crypto_Indexing_macAlg_POLY1305:
      {
        uint64_t *buf = calloc((uint32_t )5, sizeof (uint64_t ));
        r =
          (Crypto_Symmetric_MAC__buffer ){
            .tag = Crypto_Symmetric_MAC__buffer_B_POLY1305,
            { .case_B_POLY1305 = { .x00 = buf } }
          };
        break;
      }
    case Crypto_Indexing_macAlg_GHASH:
      {
        uint8_t *buf = calloc(Crypto_Symmetric_MAC_wlen, sizeof (uint8_t ));
        r =
          (Crypto_Symmetric_MAC__buffer ){
            .tag = Crypto_Symmetric_MAC__buffer_B_GHASH,
            { .case_B_GHASH = { .x10 = buf } }
          };
        break;
      }
    default:
      {
        printf("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        exit(253);
      }
  }
  uint8_t *s = calloc((uint32_t )16, sizeof (uint8_t ));
  bool scrut0 = Crypto_Symmetric_UF1CMA_skeyed(Prims_fst(macId));
  K___uint8_t__uint8_t_ scrut;
  if (scrut0 == true)
    scrut =
      (K___uint8_t__uint8_t_ ){
        .fst
        =
        Crypto_Symmetric_UF1CMA_get_skey(Crypto_Symmetric_PRF____State___mac_rgn(i,
            Crypto_AEAD_Invariant____State___prf(i, Crypto_Indexing_rw_Writer, st)),
          Prims_fst(macId),
          Crypto_AEAD_Invariant____State___ak(i, Crypto_Indexing_rw_Writer, st)),
        .snd = keyBuffer
      };
  else
  {
    bool uu____4255 = scrut0;
    scrut =
      (K___uint8_t__uint8_t_ ){ .fst = keyBuffer + (uint32_t )0, .snd = keyBuffer + (uint32_t )16 };
  }
  uint8_t *rb = scrut.fst;
  uint8_t *sb = scrut.snd;
  Crypto_Symmetric_MAC_encode_r(macId, r, rb);
  memcpy(s, sb, (uint32_t )16 * sizeof sb[0]);
  Crypto_Symmetric_UF1CMA_state____
  ak =
    {
      .x00
      =
      Crypto_Symmetric_PRF____State___mac_rgn(i,
        Crypto_AEAD_Invariant____State___prf(i, Crypto_Indexing_rw_Writer, st)),
      .x01 = r,
      .x02 = s,
      .x03 = (uint8_t )0
    };
  FStar_HyperStack_mem h1 = (void *)(uint8_t )0;
  uint8_t *cipher = cipher_tagged + (uint32_t )0;
  uint8_t *tag = cipher_tagged + plainlen;
  Crypto_Symmetric_PRF_domain____ y = Crypto_Symmetric_PRF_incr(i, x);
  Crypto_AEAD_counter_enxor(i,
    Crypto_AEAD_Invariant____State___prf(i, Crypto_Indexing_rw_Writer, st),
    y,
    plainlen,
    plainlen,
    plain,
    cipher,
    h1);
  uint64_t buf0[5];
  uint8_t buf[16];
  Crypto_Symmetric_MAC__buffer a;
  switch
  (Crypto_Symmetric_MAC_alg((K___Crypto_Indexing_id_FStar_UInt128_t ){ .fst = i, .snd = x.iv }))
  {
    case Crypto_Indexing_macAlg_POLY1305:
      {
        memset(buf0, 0, (uint32_t )5 * sizeof buf0[0]);
        a =
          (Crypto_Symmetric_MAC__buffer ){
            .tag = Crypto_Symmetric_MAC__buffer_B_POLY1305,
            { .case_B_POLY1305 = { .x00 = buf0 } }
          };
        break;
      }
    case Crypto_Indexing_macAlg_GHASH:
      {
        memset(buf, 0, (uint32_t )16 * sizeof buf[0]);
        a =
          (Crypto_Symmetric_MAC__buffer ){
            .tag = Crypto_Symmetric_MAC__buffer_B_GHASH,
            { .case_B_GHASH = { .x10 = buf } }
          };
        break;
      }
    default:
      {
        printf("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        exit(253);
      }
  }
  void *l = (uint8_t )0;
  Crypto_Symmetric_UF1CMA_accBuffer____ acc = { .x00 = a, .x01 = (uint8_t )0 };
  Crypto_AEAD_Encoding_add_bytes((K___Crypto_Indexing_id_FStar_UInt128_t ){
      .fst = i,
      .snd = x.iv
    },
    ak,
    acc,
    aadlen,
    aad);
  Crypto_AEAD_Encoding_add_bytes((K___Crypto_Indexing_id_FStar_UInt128_t ){
      .fst = i,
      .snd = x.iv
    },
    ak,
    acc,
    plainlen,
    cipher);
  uint8_t final_word[16] = { 0 };
  Crypto_Indexing_id
  id = ((K___Crypto_Indexing_id_FStar_UInt128_t ){ .fst = i, .snd = x.iv }).fst;
  switch (Crypto_Indexing_macAlg_of_id(id))
  {
    case Crypto_Indexing_macAlg_POLY1305:
      {
        Crypto_Symmetric_Bytes_store_uint32((uint32_t )4, final_word + (uint32_t )0, aadlen);
        Crypto_Symmetric_Bytes_store_uint32((uint32_t )4, final_word + (uint32_t )8, plainlen);
        break;
      }
    case Crypto_Indexing_macAlg_GHASH:
      {
        Crypto_Symmetric_Bytes_store_big32((uint32_t )4,
          final_word + (uint32_t )4,
          aadlen * (uint32_t )8);
        Crypto_Symmetric_Bytes_store_big32((uint32_t )4,
          final_word + (uint32_t )12,
          plainlen * (uint32_t )8);
        break;
      }
    default:
      {
        printf("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        exit(253);
      }
  }
  Crypto_Symmetric_UF1CMA_update((K___Crypto_Indexing_id_FStar_UInt128_t ){
      .fst = i,
      .snd = x.iv
    },
    ak,
    acc,
    final_word);
  Crypto_Symmetric_UF1CMA_accBuffer____ acc0 = acc;
  Crypto_Symmetric_UF1CMA_accBuffer____ acc1 = acc0;
  FStar_HyperStack_mem h3 = (void *)(uint8_t )0;
  Crypto_AEAD_mac_wrapper((K___Crypto_Indexing_id_FStar_UInt128_t ){ .fst = i, .snd = n },
    ak,
    acc1,
    tag);
  Crypto_AEAD_finish_after_mac(h0,
    h3,
    i,
    st,
    n,
    aadlen,
    aad,
    plainlen,
    plain,
    cipher_tagged,
    ak,
    acc1,
    tag);
}

void
Crypto_AEAD_counter_dexor(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_state____ t,
  Crypto_Symmetric_PRF_domain____ x,
  uint32_t len,
  uint8_t *plaintext,
  uint8_t *ciphertext
)
{
  if (len != (uint32_t )0)
  {
    uint32_t l = Crypto_AEAD_Invariant_min(len, Crypto_Symmetric_PRF_blocklen(i));
    uint8_t *cipher = ciphertext + (uint32_t )0;
    uint8_t *plain = Crypto_Plain_sub(i, FStar_UInt32_v(len), plaintext, (uint32_t )0, l);
    Crypto_Symmetric_PRF_prf_dexor(i, t, x, l, cipher, plain);
    uint32_t len0 = len - l;
    uint8_t *ciphertext0 = ciphertext + l;
    uint8_t *plaintext0 = Crypto_Plain_sub(i, FStar_UInt32_v(len0), plaintext, l, len0);
    Crypto_AEAD_counter_dexor(i,
      t,
      Crypto_Symmetric_PRF_incr(i, x),
      len0,
      plaintext0,
      ciphertext0);
    return;
  }
  else
    return;
}

bool
Crypto_AEAD_decrypt(
  Crypto_Indexing_id i,
  Crypto_AEAD_Invariant_state_______ st,
  FStar_UInt128_t iv,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t plainlen,
  uint8_t *plain,
  uint8_t *cipher_tagged
)
{
  Crypto_Symmetric_PRF_domain____ x = { .iv = iv, .ctr = Crypto_Symmetric_PRF_ctr_0(i) };
  FStar_Buffer_recall(Crypto_Symmetric_PRF____State___key(i,
      Crypto_AEAD_Invariant____State___prf(i, Crypto_Indexing_rw_Reader, st)));
  FStar_ST_recall_region(Crypto_Symmetric_PRF____State___mac_rgn(i,
      Crypto_AEAD_Invariant____State___prf(i, Crypto_Indexing_rw_Reader, st)));
  K___Crypto_Indexing_id_FStar_UInt128_t macId = { .fst = i, .snd = x.iv };
  uint8_t *keyBuffer = calloc(Crypto_Symmetric_UF1CMA_keylen(i), sizeof (uint8_t ));
  Crypto_Symmetric_PRF_getBlock(i,
    Crypto_AEAD_Invariant____State___prf(i, Crypto_Indexing_rw_Reader, st),
    x,
    Crypto_Symmetric_UF1CMA_keylen(i),
    keyBuffer);
  Crypto_Symmetric_MAC__buffer r;
  switch (Crypto_Symmetric_MAC_alg(macId))
  {
    case Crypto_Indexing_macAlg_POLY1305:
      {
        uint64_t *buf = calloc((uint32_t )5, sizeof (uint64_t ));
        r =
          (Crypto_Symmetric_MAC__buffer ){
            .tag = Crypto_Symmetric_MAC__buffer_B_POLY1305,
            { .case_B_POLY1305 = { .x00 = buf } }
          };
        break;
      }
    case Crypto_Indexing_macAlg_GHASH:
      {
        uint8_t *buf = calloc(Crypto_Symmetric_MAC_wlen, sizeof (uint8_t ));
        r =
          (Crypto_Symmetric_MAC__buffer ){
            .tag = Crypto_Symmetric_MAC__buffer_B_GHASH,
            { .case_B_GHASH = { .x10 = buf } }
          };
        break;
      }
    default:
      {
        printf("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        exit(253);
      }
  }
  uint8_t *s = calloc((uint32_t )16, sizeof (uint8_t ));
  bool scrut0 = Crypto_Symmetric_UF1CMA_skeyed(Prims_fst(macId));
  K___uint8_t__uint8_t_ scrut;
  if (scrut0 == true)
    scrut =
      (K___uint8_t__uint8_t_ ){
        .fst
        =
        Crypto_Symmetric_UF1CMA_get_skey(Crypto_Symmetric_PRF____State___mac_rgn(i,
            Crypto_AEAD_Invariant____State___prf(i, Crypto_Indexing_rw_Reader, st)),
          Prims_fst(macId),
          Crypto_AEAD_Invariant____State___ak(i, Crypto_Indexing_rw_Reader, st)),
        .snd = keyBuffer
      };
  else
  {
    bool uu____4255 = scrut0;
    scrut =
      (K___uint8_t__uint8_t_ ){ .fst = keyBuffer + (uint32_t )0, .snd = keyBuffer + (uint32_t )16 };
  }
  uint8_t *rb = scrut.fst;
  uint8_t *sb = scrut.snd;
  Crypto_Symmetric_MAC_encode_r(macId, r, rb);
  memcpy(s, sb, (uint32_t )16 * sizeof sb[0]);
  Crypto_Symmetric_UF1CMA_state____
  ak =
    {
      .x00
      =
      Crypto_Symmetric_PRF____State___mac_rgn(i,
        Crypto_AEAD_Invariant____State___prf(i, Crypto_Indexing_rw_Reader, st)),
      .x01 = r,
      .x02 = s,
      .x03 = (uint8_t )0
    };
  uint8_t *cipher = cipher_tagged + (uint32_t )0;
  uint8_t *tag = cipher_tagged + plainlen;
  uint64_t buf0[5];
  uint8_t buf[16];
  Crypto_Symmetric_MAC__buffer a;
  switch
  (Crypto_Symmetric_MAC_alg((K___Crypto_Indexing_id_FStar_UInt128_t ){ .fst = i, .snd = x.iv }))
  {
    case Crypto_Indexing_macAlg_POLY1305:
      {
        memset(buf0, 0, (uint32_t )5 * sizeof buf0[0]);
        a =
          (Crypto_Symmetric_MAC__buffer ){
            .tag = Crypto_Symmetric_MAC__buffer_B_POLY1305,
            { .case_B_POLY1305 = { .x00 = buf0 } }
          };
        break;
      }
    case Crypto_Indexing_macAlg_GHASH:
      {
        memset(buf, 0, (uint32_t )16 * sizeof buf[0]);
        a =
          (Crypto_Symmetric_MAC__buffer ){
            .tag = Crypto_Symmetric_MAC__buffer_B_GHASH,
            { .case_B_GHASH = { .x10 = buf } }
          };
        break;
      }
    default:
      {
        printf("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        exit(253);
      }
  }
  void *l = (uint8_t )0;
  Crypto_Symmetric_UF1CMA_accBuffer____ acc = { .x00 = a, .x01 = (uint8_t )0 };
  Crypto_AEAD_Encoding_add_bytes((K___Crypto_Indexing_id_FStar_UInt128_t ){
      .fst = i,
      .snd = x.iv
    },
    ak,
    acc,
    aadlen,
    aad);
  Crypto_AEAD_Encoding_add_bytes((K___Crypto_Indexing_id_FStar_UInt128_t ){
      .fst = i,
      .snd = x.iv
    },
    ak,
    acc,
    plainlen,
    cipher);
  uint8_t final_word[16] = { 0 };
  Crypto_Indexing_id
  id = ((K___Crypto_Indexing_id_FStar_UInt128_t ){ .fst = i, .snd = x.iv }).fst;
  switch (Crypto_Indexing_macAlg_of_id(id))
  {
    case Crypto_Indexing_macAlg_POLY1305:
      {
        Crypto_Symmetric_Bytes_store_uint32((uint32_t )4, final_word + (uint32_t )0, aadlen);
        Crypto_Symmetric_Bytes_store_uint32((uint32_t )4, final_word + (uint32_t )8, plainlen);
        break;
      }
    case Crypto_Indexing_macAlg_GHASH:
      {
        Crypto_Symmetric_Bytes_store_big32((uint32_t )4,
          final_word + (uint32_t )4,
          aadlen * (uint32_t )8);
        Crypto_Symmetric_Bytes_store_big32((uint32_t )4,
          final_word + (uint32_t )12,
          plainlen * (uint32_t )8);
        break;
      }
    default:
      {
        printf("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        exit(253);
      }
  }
  Crypto_Symmetric_UF1CMA_update((K___Crypto_Indexing_id_FStar_UInt128_t ){
      .fst = i,
      .snd = x.iv
    },
    ak,
    acc,
    final_word);
  Crypto_Symmetric_UF1CMA_accBuffer____ acc0 = acc;
  bool
  verified =
    Crypto_Symmetric_UF1CMA_verify((K___Crypto_Indexing_id_FStar_UInt128_t ){
        .fst = i,
        .snd = x.iv
      },
      ak,
      acc0,
      tag);
  if (verified)
    Crypto_AEAD_counter_dexor(i,
      Crypto_AEAD_Invariant____State___prf(i, Crypto_Indexing_rw_Reader, st),
      Crypto_Symmetric_PRF_incr(i, x),
      plainlen,
      plain,
      cipher);
  return verified;
}

