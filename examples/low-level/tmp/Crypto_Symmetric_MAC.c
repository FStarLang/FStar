#include "Crypto_Symmetric_MAC.h"

Crypto_Indexing_macAlg Crypto_Symmetric_MAC_alg(K___Crypto_Indexing_id_FStar_UInt128_t i)
{
  return Crypto_Indexing_macAlg_of_id(Prims_fst(i));
}

Prims_int Crypto_Symmetric_MAC_limb_length(Crypto_Indexing_macAlg uu___45_18)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

uint64_t *Crypto_Symmetric_MAC____B_POLY1305____0(Crypto_Symmetric_MAC__buffer projectee)
{
  if (projectee.tag == Crypto_Symmetric_MAC__buffer_B_POLY1305)
  {
    uint64_t *_0 = projectee.case_B_POLY1305.x00;
    return _0;
  }
  else
  {
    printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
    exit(255);
  }
}

uint8_t *Crypto_Symmetric_MAC____B_GHASH____0(Crypto_Symmetric_MAC__buffer projectee)
{
  if (projectee.tag == Crypto_Symmetric_MAC__buffer_B_GHASH)
  {
    uint8_t *_0 = projectee.case_B_GHASH.x10;
    return _0;
  }
  else
  {
    printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
    exit(255);
  }
}

Crypto_Symmetric_MAC__buffer
Crypto_Symmetric_MAC_reveal_elemB(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_MAC__buffer e
)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void
**Crypto_Symmetric_MAC_as_buffer(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_MAC__buffer uu___46_237
)
{
  return (void **)(uint8_t )0;
}

uint32_t Crypto_Symmetric_MAC_wlen = (uint32_t )16;

void *Crypto_Symmetric_MAC_sel_word(FStar_HyperStack_mem h, uint8_t *b)
{
  return (void *)(uint8_t )0;
}

void
Crypto_Symmetric_MAC_sel_elem(
  FStar_HyperStack_mem h,
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_MAC__buffer b
)
{
  return;
}

void
Crypto_Symmetric_MAC_encode_r(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_MAC__buffer b,
  uint8_t *raw
)
{
  if (b.tag == Crypto_Symmetric_MAC__buffer_B_POLY1305)
  {
    uint64_t *b0 = b.case_B_POLY1305.x00;
    Crypto_Symmetric_Poly1305_clamp(raw);
    Crypto_Symmetric_Poly1305_toField(b0, raw);
    return;
  }
  else if (b.tag == Crypto_Symmetric_MAC__buffer_B_GHASH)
  {
    uint8_t *b0 = b.case_B_GHASH.x10;
    memcpy(b0, raw, (uint32_t )16 * sizeof raw[0]);
  }
  else
  {
    printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
    exit(255);
  }
}

void Crypto_Symmetric_MAC_encode(K___Crypto_Indexing_id_FStar_UInt128_t i, void *w)
{
  return;
}

void Crypto_Symmetric_MAC_poly(K___Crypto_Indexing_id_FStar_UInt128_t i, void *cs, void *r)
{
  switch (Crypto_Symmetric_MAC_alg(i))
  {
    case Crypto_Indexing_macAlg_POLY1305:
      {
        (void *)Crypto_Symmetric_Poly1305_Spec_poly(cs, (Prims_nat )r);
        return;
        break;
      }
    case Crypto_Indexing_macAlg_GHASH:
      {
        (void *)Crypto_Symmetric_GF128_Spec_poly(cs, (void *)r);
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

void Crypto_Symmetric_MAC_field_add(K___Crypto_Indexing_id_FStar_UInt128_t i, void *a, void *b)
{
  switch (Crypto_Symmetric_MAC_alg(i))
  {
    case Crypto_Indexing_macAlg_POLY1305:
      {
        (void *)Crypto_Symmetric_Poly1305_Spec_field_add((Prims_nat )a, (Prims_nat )b);
        return;
        break;
      }
    case Crypto_Indexing_macAlg_GHASH:
      {
        (void *)Crypto_Symmetric_GF128_Spec_op_Plus_At((void *)a, (void *)b);
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

void Crypto_Symmetric_MAC_field_mul(K___Crypto_Indexing_id_FStar_UInt128_t i, void *a, void *b)
{
  switch (Crypto_Symmetric_MAC_alg(i))
  {
    case Crypto_Indexing_macAlg_POLY1305:
      {
        (void *)Crypto_Symmetric_Poly1305_Spec_field_mul((Prims_nat )a, (Prims_nat )b);
        return;
        break;
      }
    case Crypto_Indexing_macAlg_GHASH:
      {
        (void *)Crypto_Symmetric_GF128_Spec_op_Star_At((void *)a, (void *)b);
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

void
Crypto_Symmetric_MAC_op_Plus_At(K___Crypto_Indexing_id_FStar_UInt128_t i, void *e1, void *e2)
{
  Crypto_Symmetric_MAC_field_add(i, e1, e2);
  return;
}

void
Crypto_Symmetric_MAC_op_Star_At(K___Crypto_Indexing_id_FStar_UInt128_t i, void *e1, void *e2)
{
  Crypto_Symmetric_MAC_field_mul(i, e1, e2);
  return;
}

void
Crypto_Symmetric_MAC_update(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_MAC__buffer r,
  Crypto_Symmetric_MAC__buffer a,
  uint8_t *w
)
{
  K___Crypto_Symmetric_MAC__buffer_Crypto_Symmetric_MAC__buffer scrut = { .fst = r, .snd = a };
  if
  (scrut.fst.tag
  == Crypto_Symmetric_MAC__buffer_B_POLY1305
  && scrut.snd.tag == Crypto_Symmetric_MAC__buffer_B_POLY1305)
  {
    uint64_t *a = scrut.snd.case_B_POLY1305.x00;
    uint64_t *r = scrut.fst.case_B_POLY1305.x00;
    uint64_t e[5] = { 0 };
    Crypto_Symmetric_Poly1305_toField_plus_2_128(e, w);
    Crypto_Symmetric_Poly1305_add_and_multiply(a, e, r);
  }
  else if
  (scrut.fst.tag
  == Crypto_Symmetric_MAC__buffer_B_GHASH
  && scrut.snd.tag == Crypto_Symmetric_MAC__buffer_B_GHASH)
  {
    uint8_t *a = scrut.snd.case_B_GHASH.x10;
    uint8_t *r = scrut.fst.case_B_GHASH.x10;
    Crypto_Symmetric_GF128_add_and_multiply(a, w, r);
    return;
  }
  else
  {
    printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
    exit(255);
  }
}

uint32_t Crypto_Symmetric_MAC_taglen = (uint32_t )16;

void
*Crypto_Symmetric_MAC_mac(K___Crypto_Indexing_id_FStar_UInt128_t i, void *cs, void *r, void *s)
{
  return (void *)(uint8_t )0;
}

void
Crypto_Symmetric_MAC_finish(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  uint8_t *s,
  Crypto_Symmetric_MAC__buffer a,
  uint8_t *t
)
{
  if (a.tag == Crypto_Symmetric_MAC__buffer_B_POLY1305)
  {
    uint64_t *a0 = a.case_B_POLY1305.x00;
    Crypto_Symmetric_Poly1305_poly1305_finish(t, a0, s);
    return;
  }
  else if (a.tag == Crypto_Symmetric_MAC__buffer_B_GHASH)
  {
    uint8_t *a0 = a.case_B_GHASH.x10;
    Crypto_Symmetric_GF128_finish(a0, s);
    memcpy(t, a0, (uint32_t )16 * sizeof a0[0]);
  }
  else
  {
    printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
    exit(255);
  }
}

