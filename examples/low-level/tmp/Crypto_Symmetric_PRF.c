#include "Crypto_Symmetric_PRF.h"

uint32_t Crypto_Symmetric_PRF_blocklen(Crypto_Indexing_id i)
{
  switch (Crypto_Indexing_cipherAlg_of_id(i))
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

uint32_t Crypto_Symmetric_PRF_keylen(Crypto_Indexing_id i)
{
  switch (Crypto_Indexing_cipherAlg_of_id(i))
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

uint32_t Crypto_Symmetric_PRF_statelen(Crypto_Indexing_id i)
{
  switch (Crypto_Indexing_cipherAlg_of_id(i))
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

uint32_t Crypto_Symmetric_PRF_maxCtr(Crypto_Indexing_id i)
{
  return (uint32_t )16384 / Crypto_Symmetric_PRF_blocklen(i);
}

Crypto_Symmetric_PRF_domain____
Crypto_Symmetric_PRF_incr(Crypto_Indexing_id i, Crypto_Symmetric_PRF_domain____ x)
{
  return (Crypto_Symmetric_PRF_domain____ ){ .iv = x.iv, .ctr = x.ctr + (uint32_t )1 };
}

bool
Crypto_Symmetric_PRF_above(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_domain____ x,
  Crypto_Symmetric_PRF_domain____ z
)
{
  return x.iv == z.iv && x.ctr >= z.ctr;
}

uint32_t
Crypto_Symmetric_PRF____OTP___l(Crypto_Indexing_id i, Crypto_Symmetric_PRF_otp____ projectee)
{
  Crypto_Symmetric_PRF_otp____ scrut = projectee;
  uint32_t l = scrut.x00;
  void *_1 = scrut.x01;
  void *cipher = scrut.x02;
  return l;
}

void
*Crypto_Symmetric_PRF____OTP____1(Crypto_Indexing_id i, Crypto_Symmetric_PRF_otp____ projectee)
{
  Crypto_Symmetric_PRF_otp____ scrut = projectee;
  uint32_t l = scrut.x00;
  void *_1 = scrut.x01;
  void *cipher = scrut.x02;
  return _1;
}

void
*Crypto_Symmetric_PRF____OTP___cipher(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_otp____ projectee
)
{
  Crypto_Symmetric_PRF_otp____ scrut = projectee;
  uint32_t l = scrut.x00;
  void *_1 = scrut.x01;
  void *cipher = scrut.x02;
  return cipher;
}

uint32_t Crypto_Symmetric_PRF_ctr_0(Crypto_Indexing_id i)
{
  if (Crypto_Symmetric_UF1CMA_skeyed(i))
    return (uint32_t )1;
  else
    return (uint32_t )0;
}

FStar_UInt128_t Crypto_Symmetric_PRF_iv_0 = FStar_Int_Cast_uint64_to_uint128((uint64_t )0);

uint8_t
*Crypto_Symmetric_PRF_sk0Range(
  FStar_HyperHeap_rid rgn,
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_domain____ x,
  void *z
)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Crypto_Symmetric_UF1CMA_state____
Crypto_Symmetric_PRF_macRange(
  FStar_HyperHeap_rid rgn,
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_domain____ x,
  void *z
)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Crypto_Symmetric_PRF_otp____
Crypto_Symmetric_PRF_otpRange(
  FStar_HyperHeap_rid rgn,
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_domain____ x,
  void *z
)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void
*Crypto_Symmetric_PRF_blkRange(
  FStar_HyperHeap_rid rgn,
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_domain____ x,
  void *z
)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Crypto_Symmetric_PRF_domain____
Crypto_Symmetric_PRF____Entry___x(
  FStar_HyperHeap_rid rgn,
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_entry_______ projectee
)
{
  Crypto_Symmetric_PRF_entry_______ scrut = projectee;
  Crypto_Symmetric_PRF_domain____ x = scrut.x00;
  void *range = scrut.x01;
  return x;
}

void
Crypto_Symmetric_PRF____Entry___range(
  FStar_HyperHeap_rid rgn,
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_entry_______ projectee
)
{
  Crypto_Symmetric_PRF_entry_______ scrut = projectee;
  Crypto_Symmetric_PRF_domain____ x = scrut.x00;
  void *range = scrut.x01;
  return;
}

bool
Crypto_Symmetric_PRF_is_entry_domain(
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid rgn,
  Crypto_Symmetric_PRF_domain____ x,
  Crypto_Symmetric_PRF_entry_______ e
)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_option____
Crypto_Symmetric_PRF_find(
  FStar_HyperHeap_rid rgn,
  Crypto_Indexing_id i,
  void *s,
  Crypto_Symmetric_PRF_domain____ x
)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_option__uint8_t_
Crypto_Symmetric_PRF_find_sk0(
  FStar_HyperHeap_rid rgn,
  Crypto_Indexing_id i,
  void *s,
  Crypto_Symmetric_PRF_domain____ x
)
{
  Prims_option____ scrut = Crypto_Symmetric_PRF_find(rgn, i, s, x);
  if (scrut.tag == Prims_option_____Some)
  {
    void *v = scrut.case_Some.v;
    return
      (Prims_option__uint8_t_ ){
        .tag = Prims_option__uint8_t__Some,
        { .case_Some = { .v = Crypto_Symmetric_PRF_sk0Range(rgn, i, x, v) } }
      };
  }
  else if (scrut.tag == Prims_option_____None)
    return (Prims_option__uint8_t_ ){ .tag = Prims_option__uint8_t__None, { .case_None = {  } } };
  else
  {
    printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
    exit(255);
  }
}

Prims_option__Crypto_Symmetric_UF1CMA_state____
Crypto_Symmetric_PRF_find_mac(
  FStar_HyperHeap_rid rgn,
  Crypto_Indexing_id i,
  void *s,
  Crypto_Symmetric_PRF_domain____ x
)
{
  Prims_option____ scrut = Crypto_Symmetric_PRF_find(rgn, i, s, x);
  if (scrut.tag == Prims_option_____Some)
  {
    void *v = scrut.case_Some.v;
    return
      (Prims_option__Crypto_Symmetric_UF1CMA_state____ ){
        .tag = Prims_option__Crypto_Symmetric_UF1CMA_state_____Some,
        { .case_Some = { .v = Crypto_Symmetric_PRF_macRange(rgn, i, x, v) } }
      };
  }
  else if (scrut.tag == Prims_option_____None)
    return
      (Prims_option__Crypto_Symmetric_UF1CMA_state____ ){
        .tag = Prims_option__Crypto_Symmetric_UF1CMA_state_____None,
        { .case_None = {  } }
      };
  else
  {
    printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
    exit(255);
  }
}

Prims_option__Crypto_Symmetric_PRF_otp____
Crypto_Symmetric_PRF_find_otp(
  FStar_HyperHeap_rid rgn,
  Crypto_Indexing_id i,
  void *s,
  Crypto_Symmetric_PRF_domain____ x
)
{
  Prims_option____ scrut = Crypto_Symmetric_PRF_find(rgn, i, s, x);
  if (scrut.tag == Prims_option_____Some)
  {
    void *v = scrut.case_Some.v;
    return
      (Prims_option__Crypto_Symmetric_PRF_otp____ ){
        .tag = Prims_option__Crypto_Symmetric_PRF_otp_____Some,
        { .case_Some = { .v = Crypto_Symmetric_PRF_otpRange(rgn, i, x, v) } }
      };
  }
  else if (scrut.tag == Prims_option_____None)
    return
      (Prims_option__Crypto_Symmetric_PRF_otp____ ){
        .tag = Prims_option__Crypto_Symmetric_PRF_otp_____None,
        { .case_None = {  } }
      };
  else
  {
    printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
    exit(255);
  }
}

Prims_option__FStar_Seq_seq_uint8_t
Crypto_Symmetric_PRF_find_blk(
  FStar_HyperHeap_rid rgn,
  Crypto_Indexing_id i,
  void *s,
  Crypto_Symmetric_PRF_domain____ x
)
{
  Prims_option____ scrut = Crypto_Symmetric_PRF_find(rgn, i, s, x);
  if (scrut.tag == Prims_option_____Some)
  {
    void *v = scrut.case_Some.v;
    return
      (Prims_option__FStar_Seq_seq_uint8_t ){
        .tag = Prims_option__FStar_Seq_seq_uint8_t_Some,
        { .case_Some = { .v = Crypto_Symmetric_PRF_blkRange(rgn, i, x, v) } }
      };
  }
  else if (scrut.tag == Prims_option_____None)
    return
      (Prims_option__FStar_Seq_seq_uint8_t ){
        .tag = Prims_option__FStar_Seq_seq_uint8_t_None,
        { .case_None = {  } }
      };
  else
  {
    printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
    exit(255);
  }
}

FStar_HyperHeap_rid
Crypto_Symmetric_PRF____State___rgn(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_state____ projectee
)
{
  Crypto_Symmetric_PRF_state____ scrut = projectee;
  FStar_HyperHeap_rid rgn = scrut.x00;
  FStar_HyperHeap_rid mac_rgn = scrut.x01;
  uint8_t *key = scrut.x02;
  void *table = scrut.x03;
  return rgn;
}

FStar_HyperHeap_rid
Crypto_Symmetric_PRF____State___mac_rgn(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_state____ projectee
)
{
  Crypto_Symmetric_PRF_state____ scrut = projectee;
  FStar_HyperHeap_rid rgn = scrut.x00;
  FStar_HyperHeap_rid mac_rgn = scrut.x01;
  uint8_t *key = scrut.x02;
  void *table = scrut.x03;
  return mac_rgn;
}

uint8_t
*Crypto_Symmetric_PRF____State___key(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_state____ projectee
)
{
  Crypto_Symmetric_PRF_state____ scrut = projectee;
  FStar_HyperHeap_rid rgn = scrut.x00;
  FStar_HyperHeap_rid mac_rgn = scrut.x01;
  uint8_t *key = scrut.x02;
  void *table = scrut.x03;
  return key;
}

void
Crypto_Symmetric_PRF____State___table(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_state____ projectee
)
{
  Crypto_Symmetric_PRF_state____ scrut = projectee;
  FStar_HyperHeap_rid rgn = scrut.x00;
  FStar_HyperHeap_rid mac_rgn = scrut.x01;
  uint8_t *key = scrut.x02;
  void *table = scrut.x03;
  return;
}

void *Crypto_Symmetric_PRF_itable(Crypto_Indexing_id i, Crypto_Symmetric_PRF_state____ s)
{
  return Crypto_Symmetric_PRF____State___table(i, s) , (void *)0;
}

void
Crypto_Symmetric_PRF_mktable(
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid rgn,
  FStar_HyperHeap_rid mac_rgn,
  void *r
)
{
  return;
}

void
Crypto_Symmetric_PRF_no_table(
  Crypto_Indexing_id i,
  FStar_HyperHeap_rid rgn,
  FStar_HyperHeap_rid mac_rgn
)
{
  return;
}

uint8_t *Crypto_Symmetric_PRF_leak(Crypto_Indexing_id i, Crypto_Symmetric_PRF_state____ st)
{
  FStar_Buffer_recall(Crypto_Symmetric_PRF____State___key(i, st));
  return Crypto_Symmetric_PRF____State___key(i, st);
}

void
Crypto_Symmetric_PRF_getBlock(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_state____ t,
  Crypto_Symmetric_PRF_domain____ x,
  uint32_t len,
  uint8_t *output
)
{
  FStar_Buffer_recall(Crypto_Symmetric_PRF____State___key(i, t));
  Crypto_Symmetric_Cipher_compute(Crypto_Indexing_cipherAlg_of_id(i),
    output,
    Crypto_Symmetric_PRF____State___key(i, t),
    x.iv,
    x.ctr,
    len);
  return;
}

Prims_int Crypto_Symmetric_PRF_zero;

void
Crypto_Symmetric_PRF_prf_blk(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_state____ t,
  Crypto_Symmetric_PRF_domain____ x,
  uint32_t len,
  uint8_t *output
)
{
  Crypto_Symmetric_PRF_getBlock(i, t, x, len, output);
  return;
}

void
Crypto_Symmetric_PRF_prf_dexor(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_state____ t,
  Crypto_Symmetric_PRF_domain____ x,
  uint32_t l,
  uint8_t *cipher,
  uint8_t *plain
)
{
  uint8_t *plainrepr = Crypto_Plain_bufferRepr(i, FStar_UInt32_v(l), plain);
  Crypto_Symmetric_PRF_prf_blk(i, t, x, l, plainrepr);
  Buffer_Utils_xor_bytes_inplace(plainrepr, cipher, l);
  return;
}

void
Crypto_Symmetric_PRF_prf_enxor(
  Crypto_Indexing_id i,
  Crypto_Symmetric_PRF_state____ t,
  Crypto_Symmetric_PRF_domain____ x,
  uint32_t l,
  uint8_t *cipher,
  uint8_t *plain
)
{
  uint8_t *plainrepr = Crypto_Plain_bufferRepr(i, FStar_UInt32_v(l), plain);
  Crypto_Symmetric_PRF_prf_blk(i, t, x, l, cipher);
  Buffer_Utils_xor_bytes_inplace(cipher, plainrepr, l);
  return;
}

