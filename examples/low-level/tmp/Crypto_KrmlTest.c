#include "Crypto_KrmlTest.h"

void tweak(uint32_t pos, uint8_t *b)
{
  uint8_t _0_140 = b[pos];
  uint8_t _0_141 = _0_140 ^ (uint8_t )42;
  b[pos] = _0_141;
}

bool test()
{
  uint32_t plainlen = (uint32_t )114;
  uint8_t
  plainrepr[114] =
    {
      (uint8_t )0x4c,
      (uint8_t )0x61,
      (uint8_t )0x64,
      (uint8_t )0x69,
      (uint8_t )0x65,
      (uint8_t )0x73,
      (uint8_t )0x20,
      (uint8_t )0x61,
      (uint8_t )0x6e,
      (uint8_t )0x64,
      (uint8_t )0x20,
      (uint8_t )0x47,
      (uint8_t )0x65,
      (uint8_t )0x6e,
      (uint8_t )0x74,
      (uint8_t )0x6c,
      (uint8_t )0x65,
      (uint8_t )0x6d,
      (uint8_t )0x65,
      (uint8_t )0x6e,
      (uint8_t )0x20,
      (uint8_t )0x6f,
      (uint8_t )0x66,
      (uint8_t )0x20,
      (uint8_t )0x74,
      (uint8_t )0x68,
      (uint8_t )0x65,
      (uint8_t )0x20,
      (uint8_t )0x63,
      (uint8_t )0x6c,
      (uint8_t )0x61,
      (uint8_t )0x73,
      (uint8_t )0x73,
      (uint8_t )0x20,
      (uint8_t )0x6f,
      (uint8_t )0x66,
      (uint8_t )0x20,
      (uint8_t )0x27,
      (uint8_t )0x39,
      (uint8_t )0x39,
      (uint8_t )0x3a,
      (uint8_t )0x20,
      (uint8_t )0x49,
      (uint8_t )0x66,
      (uint8_t )0x20,
      (uint8_t )0x49,
      (uint8_t )0x20,
      (uint8_t )0x63,
      (uint8_t )0x6f,
      (uint8_t )0x75,
      (uint8_t )0x6c,
      (uint8_t )0x64,
      (uint8_t )0x20,
      (uint8_t )0x6f,
      (uint8_t )0x66,
      (uint8_t )0x66,
      (uint8_t )0x65,
      (uint8_t )0x72,
      (uint8_t )0x20,
      (uint8_t )0x79,
      (uint8_t )0x6f,
      (uint8_t )0x75,
      (uint8_t )0x20,
      (uint8_t )0x6f,
      (uint8_t )0x6e,
      (uint8_t )0x6c,
      (uint8_t )0x79,
      (uint8_t )0x20,
      (uint8_t )0x6f,
      (uint8_t )0x6e,
      (uint8_t )0x65,
      (uint8_t )0x20,
      (uint8_t )0x74,
      (uint8_t )0x69,
      (uint8_t )0x70,
      (uint8_t )0x20,
      (uint8_t )0x66,
      (uint8_t )0x6f,
      (uint8_t )0x72,
      (uint8_t )0x20,
      (uint8_t )0x74,
      (uint8_t )0x68,
      (uint8_t )0x65,
      (uint8_t )0x20,
      (uint8_t )0x66,
      (uint8_t )0x75,
      (uint8_t )0x74,
      (uint8_t )0x75,
      (uint8_t )0x72,
      (uint8_t )0x65,
      (uint8_t )0x2c,
      (uint8_t )0x20,
      (uint8_t )0x73,
      (uint8_t )0x75,
      (uint8_t )0x6e,
      (uint8_t )0x73,
      (uint8_t )0x63,
      (uint8_t )0x72,
      (uint8_t )0x65,
      (uint8_t )0x65,
      (uint8_t )0x6e,
      (uint8_t )0x20,
      (uint8_t )0x77,
      (uint8_t )0x6f,
      (uint8_t )0x75,
      (uint8_t )0x6c,
      (uint8_t )0x64,
      (uint8_t )0x20,
      (uint8_t )0x62,
      (uint8_t )0x65,
      (uint8_t )0x20,
      (uint8_t )0x69,
      (uint8_t )0x74,
      (uint8_t )0x2e
    };
  Crypto_Indexing_id i = Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_CHACHA20_POLY1305);
  uint8_t *plain = Crypto_Plain_unsafe_hide_buffer(i, FStar_UInt32_v(plainlen), plainrepr);
  uint8_t
  buf0[12] =
    {
      (uint8_t )0x50,
      (uint8_t )0x51,
      (uint8_t )0x52,
      (uint8_t )0x53,
      (uint8_t )0xc0,
      (uint8_t )0xc1,
      (uint8_t )0xc2,
      (uint8_t )0xc3,
      (uint8_t )0xc4,
      (uint8_t )0xc5,
      (uint8_t )0xc6,
      (uint8_t )0xc7
    };
  uint8_t *aad = buf0;
  uint32_t aadlen = (uint32_t )12;
  uint8_t
  buf1[32] =
    {
      (uint8_t )0x80,
      (uint8_t )0x81,
      (uint8_t )0x82,
      (uint8_t )0x83,
      (uint8_t )0x84,
      (uint8_t )0x85,
      (uint8_t )0x86,
      (uint8_t )0x87,
      (uint8_t )0x88,
      (uint8_t )0x89,
      (uint8_t )0x8a,
      (uint8_t )0x8b,
      (uint8_t )0x8c,
      (uint8_t )0x8d,
      (uint8_t )0x8e,
      (uint8_t )0x8f,
      (uint8_t )0x90,
      (uint8_t )0x91,
      (uint8_t )0x92,
      (uint8_t )0x93,
      (uint8_t )0x94,
      (uint8_t )0x95,
      (uint8_t )0x96,
      (uint8_t )0x97,
      (uint8_t )0x98,
      (uint8_t )0x99,
      (uint8_t )0x9a,
      (uint8_t )0x9b,
      (uint8_t )0x9c,
      (uint8_t )0x9d,
      (uint8_t )0x9e,
      (uint8_t )0x9f
    };
  uint8_t *key = buf1;
  uint8_t
  buf2[12] =
    {
      (uint8_t )0x07,
      (uint8_t )0x00,
      (uint8_t )0x00,
      (uint8_t )0x00,
      (uint8_t )0x40,
      (uint8_t )0x41,
      (uint8_t )0x42,
      (uint8_t )0x43,
      (uint8_t )0x44,
      (uint8_t )0x45,
      (uint8_t )0x46,
      (uint8_t )0x47
    };
  uint8_t *ivBuffer = buf2;
  Crypto_Symmetric_Bytes_lemma_little_endian_is_bounded(Crypto_Symmetric_Bytes_load_bytes((uint32_t )12,
      ivBuffer));
  FStar_UInt128_t iv = Crypto_Symmetric_Bytes_load_uint128((uint32_t )12, ivBuffer);
  uint8_t
  buf[130] =
    {
      (uint8_t )0xd3,
      (uint8_t )0x1a,
      (uint8_t )0x8d,
      (uint8_t )0x34,
      (uint8_t )0x64,
      (uint8_t )0x8e,
      (uint8_t )0x60,
      (uint8_t )0xdb,
      (uint8_t )0x7b,
      (uint8_t )0x86,
      (uint8_t )0xaf,
      (uint8_t )0xbc,
      (uint8_t )0x53,
      (uint8_t )0xef,
      (uint8_t )0x7e,
      (uint8_t )0xc2,
      (uint8_t )0xa4,
      (uint8_t )0xad,
      (uint8_t )0xed,
      (uint8_t )0x51,
      (uint8_t )0x29,
      (uint8_t )0x6e,
      (uint8_t )0x08,
      (uint8_t )0xfe,
      (uint8_t )0xa9,
      (uint8_t )0xe2,
      (uint8_t )0xb5,
      (uint8_t )0xa7,
      (uint8_t )0x36,
      (uint8_t )0xee,
      (uint8_t )0x62,
      (uint8_t )0xd6,
      (uint8_t )0x3d,
      (uint8_t )0xbe,
      (uint8_t )0xa4,
      (uint8_t )0x5e,
      (uint8_t )0x8c,
      (uint8_t )0xa9,
      (uint8_t )0x67,
      (uint8_t )0x12,
      (uint8_t )0x82,
      (uint8_t )0xfa,
      (uint8_t )0xfb,
      (uint8_t )0x69,
      (uint8_t )0xda,
      (uint8_t )0x92,
      (uint8_t )0x72,
      (uint8_t )0x8b,
      (uint8_t )0x1a,
      (uint8_t )0x71,
      (uint8_t )0xde,
      (uint8_t )0x0a,
      (uint8_t )0x9e,
      (uint8_t )0x06,
      (uint8_t )0x0b,
      (uint8_t )0x29,
      (uint8_t )0x05,
      (uint8_t )0xd6,
      (uint8_t )0xa5,
      (uint8_t )0xb6,
      (uint8_t )0x7e,
      (uint8_t )0xcd,
      (uint8_t )0x3b,
      (uint8_t )0x36,
      (uint8_t )0x92,
      (uint8_t )0xdd,
      (uint8_t )0xbd,
      (uint8_t )0x7f,
      (uint8_t )0x2d,
      (uint8_t )0x77,
      (uint8_t )0x8b,
      (uint8_t )0x8c,
      (uint8_t )0x98,
      (uint8_t )0x03,
      (uint8_t )0xae,
      (uint8_t )0xe3,
      (uint8_t )0x28,
      (uint8_t )0x09,
      (uint8_t )0x1b,
      (uint8_t )0x58,
      (uint8_t )0xfa,
      (uint8_t )0xb3,
      (uint8_t )0x24,
      (uint8_t )0xe4,
      (uint8_t )0xfa,
      (uint8_t )0xd6,
      (uint8_t )0x75,
      (uint8_t )0x94,
      (uint8_t )0x55,
      (uint8_t )0x85,
      (uint8_t )0x80,
      (uint8_t )0x8b,
      (uint8_t )0x48,
      (uint8_t )0x31,
      (uint8_t )0xd7,
      (uint8_t )0xbc,
      (uint8_t )0x3f,
      (uint8_t )0xf4,
      (uint8_t )0xde,
      (uint8_t )0xf0,
      (uint8_t )0x8e,
      (uint8_t )0x4b,
      (uint8_t )0x7a,
      (uint8_t )0x9d,
      (uint8_t )0xe5,
      (uint8_t )0x76,
      (uint8_t )0xd2,
      (uint8_t )0x65,
      (uint8_t )0x86,
      (uint8_t )0xce,
      (uint8_t )0xc6,
      (uint8_t )0x4b,
      (uint8_t )0x61,
      (uint8_t )0x16,
      (uint8_t )0x1a,
      (uint8_t )0xe1,
      (uint8_t )0x0b,
      (uint8_t )0x59,
      (uint8_t )0x4f,
      (uint8_t )0x09,
      (uint8_t )0xe2,
      (uint8_t )0x6a,
      (uint8_t )0x7e,
      (uint8_t )0x90,
      (uint8_t )0x2e,
      (uint8_t )0xcb,
      (uint8_t )0xd0,
      (uint8_t )0x60,
      (uint8_t )0x06,
      (uint8_t )0x91
    };
  uint8_t *expected_cipher = buf;
  uint32_t cipherlen = plainlen + (uint32_t )16;
  uint8_t cipher[cipherlen];
  memset(cipher, 0, cipherlen * sizeof cipher[0]);
  FStar_HyperHeap_rid mac_rgn = FStar_ST_new_region(FStar_HyperHeap_root);
  uint8_t *keystate = calloc(Crypto_Symmetric_PRF_statelen(i), sizeof (uint8_t ));
  Crypto_Indexing_cipherAlg alg = Crypto_Indexing_cipherAlg_of_id(i);
  Crypto_Symmetric_Cipher_init(alg, key, keystate);
  Crypto_Symmetric_PRF_state____
  prf =
    {
      .x00 = FStar_HyperHeap_root,
      .x01 = mac_rgn,
      .x02 = keystate,
      .x03 = (Crypto_Symmetric_PRF_no_table(i, FStar_HyperHeap_root, mac_rgn) , (void *)0)
    };
  void *log = FStar_ST_ralloc(FStar_HyperHeap_root, FStar_Seq_createEmpty((uint8_t )0));
  Prims_option__uint8_t_ ak;
  if (Crypto_Symmetric_UF1CMA_skeyed(i))
  {
    Crypto_Symmetric_PRF_domain____ x = { .iv = Crypto_Symmetric_PRF_iv_0, .ctr = (uint32_t )0 };
    uint8_t *keyBuffer = calloc(Crypto_Symmetric_UF1CMA_skeylen(i), sizeof (uint8_t ));
    Crypto_Symmetric_PRF_getBlock(i, prf, x, Crypto_Symmetric_UF1CMA_skeylen(i), keyBuffer);
    ak =
      (Prims_option__uint8_t_ ){
        .tag = Prims_option__uint8_t__Some,
        { .case_Some = { .v = keyBuffer } }
      };
  }
  else
    ak = (Prims_option__uint8_t_ ){ .tag = Prims_option__uint8_t__None, { .case_None = {  } } };
  Crypto_AEAD_Invariant_state_______
  st0 = { .x00 = FStar_HyperHeap_root, .x01 = log, .x02 = prf, .x03 = ak };
  Crypto_AEAD_encrypt(i, st0, iv, aadlen, aad, plainlen, plain, cipher);
  int8_t
  string_cipher[7] =
    {
      (int8_t )99,
      (int8_t )105,
      (int8_t )112,
      (int8_t )104,
      (int8_t )101,
      (int8_t )114,
      (int8_t )0
    };
  uint8_t buf3[plainlen];
  memset(buf3, 0, plainlen * sizeof buf3[0]);
  uint8_t *decrypted = buf3;
  Crypto_AEAD_Invariant_state_______ st = Crypto_AEAD_genReader(i, st0);
  bool ok_1 = Crypto_AEAD_decrypt(i, st, iv, aadlen, aad, plainlen, decrypted, cipher);
  int8_t
  string_decryption[11] =
    {
      (int8_t )100,
      (int8_t )101,
      (int8_t )99,
      (int8_t )114,
      (int8_t )121,
      (int8_t )112,
      (int8_t )116,
      (int8_t )105,
      (int8_t )111,
      (int8_t )110,
      (int8_t )0
    };
  bool
  fail_0 =
    Crypto_AEAD_decrypt(i,
      st,
      iv,
      aadlen - (uint32_t )1,
      aad + (uint32_t )0,
      plainlen,
      decrypted,
      cipher);
  tweak((uint32_t )3, cipher);
  bool fail_1 = Crypto_AEAD_decrypt(i, st, iv, aadlen, aad, plainlen, decrypted, cipher);
  tweak((uint32_t )3, cipher);
  tweak(plainlen, cipher);
  bool fail_2 = Crypto_AEAD_decrypt(i, st, iv, aadlen, aad, plainlen, decrypted, cipher);
  tweak(plainlen, cipher);
  return ok_1 && !(fail_0 || fail_1 || fail_2);
}

bool
test_aes_gcm(
  Crypto_Indexing_id i,
  uint32_t tn,
  uint8_t *key,
  uint8_t *ivBuffer,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t plainlen,
  uint8_t *plainrepr,
  uint8_t *expected_cipher
)
{
  uint8_t *plain = Crypto_Plain_unsafe_hide_buffer(i, FStar_UInt32_v(plainlen), plainrepr);
  FStar_HyperHeap_rid mac_rgn = FStar_ST_new_region(FStar_HyperHeap_root);
  uint8_t *keystate = calloc(Crypto_Symmetric_PRF_statelen(i), sizeof (uint8_t ));
  Crypto_Indexing_cipherAlg alg = Crypto_Indexing_cipherAlg_of_id(i);
  Crypto_Symmetric_Cipher_init(alg, key, keystate);
  Crypto_Symmetric_PRF_state____
  prf =
    {
      .x00 = FStar_HyperHeap_root,
      .x01 = mac_rgn,
      .x02 = keystate,
      .x03 = (Crypto_Symmetric_PRF_no_table(i, FStar_HyperHeap_root, mac_rgn) , (void *)0)
    };
  void *log = FStar_ST_ralloc(FStar_HyperHeap_root, FStar_Seq_createEmpty((uint8_t )0));
  Prims_option__uint8_t_ ak;
  if (Crypto_Symmetric_UF1CMA_skeyed(i))
  {
    Crypto_Symmetric_PRF_domain____ x = { .iv = Crypto_Symmetric_PRF_iv_0, .ctr = (uint32_t )0 };
    uint8_t *keyBuffer = calloc(Crypto_Symmetric_UF1CMA_skeylen(i), sizeof (uint8_t ));
    Crypto_Symmetric_PRF_getBlock(i, prf, x, Crypto_Symmetric_UF1CMA_skeylen(i), keyBuffer);
    ak =
      (Prims_option__uint8_t_ ){
        .tag = Prims_option__uint8_t__Some,
        { .case_Some = { .v = keyBuffer } }
      };
  }
  else
    ak = (Prims_option__uint8_t_ ){ .tag = Prims_option__uint8_t__None, { .case_None = {  } } };
  Crypto_AEAD_Invariant_state_______
  st = { .x00 = FStar_HyperHeap_root, .x01 = log, .x02 = prf, .x03 = ak };
  Crypto_Symmetric_Bytes_lemma_little_endian_is_bounded(Crypto_Symmetric_Bytes_load_bytes((uint32_t )12,
      ivBuffer));
  FStar_UInt128_t iv = Crypto_Symmetric_Bytes_load_uint128((uint32_t )12, ivBuffer);
  uint32_t cipherlen = plainlen + (uint32_t )16;
  uint8_t cipher[cipherlen];
  for (uintmax_t i = 0; i < cipherlen; ++i)
    cipher[i] = (uint8_t )2;
  Crypto_AEAD_encrypt(i, st, iv, aadlen, aad, plainlen, plain, cipher);
  int8_t
  string_cipher[7] =
    {
      (int8_t )99,
      (int8_t )105,
      (int8_t )112,
      (int8_t )104,
      (int8_t )101,
      (int8_t )114,
      (int8_t )0
    };
  Crypto_AEAD_Invariant_state_______ st0 = Crypto_AEAD_genReader(i, st);
  uint8_t buf[plainlen];
  for (uintmax_t i = 0; i < plainlen; ++i)
    buf[i] = (uint8_t )3;
  uint8_t *decrypted = buf;
  bool ok_1 = Crypto_AEAD_decrypt(i, st0, iv, aadlen, aad, plainlen, decrypted, cipher);
  int8_t
  string_decryption[11] =
    {
      (int8_t )100,
      (int8_t )101,
      (int8_t )99,
      (int8_t )114,
      (int8_t )121,
      (int8_t )112,
      (int8_t )116,
      (int8_t )105,
      (int8_t )111,
      (int8_t )110,
      (int8_t )0
    };
  return ok_1;
}

int32_t main()
{
  bool uu____15454 = test();
  Crypto_Indexing_id i = Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_AES_256_GCM);
  uint8_t k0[32] = { 0 };
  uint32_t plainlen0 = (uint32_t )0;
  uint8_t plain0[plainlen0];
  memset(plain0, 0, plainlen0 * sizeof plain0[0]);
  uint8_t iv0[12] = { 0 };
  uint32_t aadlen0 = (uint32_t )0;
  uint8_t aad0[aadlen0];
  memset(aad0, 0, aadlen0 * sizeof aad0[0]);
  uint8_t
  cipher0[16] =
    {
      (uint8_t )0x53,
      (uint8_t )0x0f,
      (uint8_t )0x8a,
      (uint8_t )0xfb,
      (uint8_t )0xc7,
      (uint8_t )0x45,
      (uint8_t )0x36,
      (uint8_t )0xb9,
      (uint8_t )0xa9,
      (uint8_t )0x63,
      (uint8_t )0xb4,
      (uint8_t )0xf1,
      (uint8_t )0xc4,
      (uint8_t )0xcb,
      (uint8_t )0x73,
      (uint8_t )0x8b
    };
  bool
  uu____15455 = test_aes_gcm(i, (uint32_t )1, k0, iv0, aadlen0, aad0, plainlen0, plain0, cipher0);
  Crypto_Indexing_id i0 = Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_AES_256_GCM);
  uint8_t k1[32] = { 0 };
  uint32_t plainlen1 = (uint32_t )16;
  uint8_t plain1[plainlen1];
  memset(plain1, 0, plainlen1 * sizeof plain1[0]);
  uint8_t iv1[12] = { 0 };
  uint32_t aadlen1 = (uint32_t )0;
  uint8_t aad1[aadlen1];
  memset(aad1, 0, aadlen1 * sizeof aad1[0]);
  uint8_t
  cipher1[32] =
    {
      (uint8_t )0xce,
      (uint8_t )0xa7,
      (uint8_t )0x40,
      (uint8_t )0x3d,
      (uint8_t )0x4d,
      (uint8_t )0x60,
      (uint8_t )0x6b,
      (uint8_t )0x6e,
      (uint8_t )0x07,
      (uint8_t )0x4e,
      (uint8_t )0xc5,
      (uint8_t )0xd3,
      (uint8_t )0xba,
      (uint8_t )0xf3,
      (uint8_t )0x9d,
      (uint8_t )0x18,
      (uint8_t )0xd0,
      (uint8_t )0xd1,
      (uint8_t )0xc8,
      (uint8_t )0xa7,
      (uint8_t )0x99,
      (uint8_t )0x99,
      (uint8_t )0x6b,
      (uint8_t )0xf0,
      (uint8_t )0x26,
      (uint8_t )0x5b,
      (uint8_t )0x98,
      (uint8_t )0xb5,
      (uint8_t )0xd4,
      (uint8_t )0x8a,
      (uint8_t )0xb9,
      (uint8_t )0x19
    };
  bool
  uu____15456 =
    test_aes_gcm(i0,
      (uint32_t )2,
      k1,
      iv1,
      aadlen1,
      aad1,
      plainlen1,
      plain1,
      cipher1);
  Crypto_Indexing_id i1 = Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_AES_256_GCM);
  uint8_t
  k2[32] =
    {
      (uint8_t )0xfe,
      (uint8_t )0xff,
      (uint8_t )0xe9,
      (uint8_t )0x92,
      (uint8_t )0x86,
      (uint8_t )0x65,
      (uint8_t )0x73,
      (uint8_t )0x1c,
      (uint8_t )0x6d,
      (uint8_t )0x6a,
      (uint8_t )0x8f,
      (uint8_t )0x94,
      (uint8_t )0x67,
      (uint8_t )0x30,
      (uint8_t )0x83,
      (uint8_t )0x08,
      (uint8_t )0xfe,
      (uint8_t )0xff,
      (uint8_t )0xe9,
      (uint8_t )0x92,
      (uint8_t )0x86,
      (uint8_t )0x65,
      (uint8_t )0x73,
      (uint8_t )0x1c,
      (uint8_t )0x6d,
      (uint8_t )0x6a,
      (uint8_t )0x8f,
      (uint8_t )0x94,
      (uint8_t )0x67,
      (uint8_t )0x30,
      (uint8_t )0x83,
      (uint8_t )0x08
    };
  uint32_t plainlen2 = (uint32_t )64;
  uint8_t
  plain2[64] =
    {
      (uint8_t )0xd9,
      (uint8_t )0x31,
      (uint8_t )0x32,
      (uint8_t )0x25,
      (uint8_t )0xf8,
      (uint8_t )0x84,
      (uint8_t )0x06,
      (uint8_t )0xe5,
      (uint8_t )0xa5,
      (uint8_t )0x59,
      (uint8_t )0x09,
      (uint8_t )0xc5,
      (uint8_t )0xaf,
      (uint8_t )0xf5,
      (uint8_t )0x26,
      (uint8_t )0x9a,
      (uint8_t )0x86,
      (uint8_t )0xa7,
      (uint8_t )0xa9,
      (uint8_t )0x53,
      (uint8_t )0x15,
      (uint8_t )0x34,
      (uint8_t )0xf7,
      (uint8_t )0xda,
      (uint8_t )0x2e,
      (uint8_t )0x4c,
      (uint8_t )0x30,
      (uint8_t )0x3d,
      (uint8_t )0x8a,
      (uint8_t )0x31,
      (uint8_t )0x8a,
      (uint8_t )0x72,
      (uint8_t )0x1c,
      (uint8_t )0x3c,
      (uint8_t )0x0c,
      (uint8_t )0x95,
      (uint8_t )0x95,
      (uint8_t )0x68,
      (uint8_t )0x09,
      (uint8_t )0x53,
      (uint8_t )0x2f,
      (uint8_t )0xcf,
      (uint8_t )0x0e,
      (uint8_t )0x24,
      (uint8_t )0x49,
      (uint8_t )0xa6,
      (uint8_t )0xb5,
      (uint8_t )0x25,
      (uint8_t )0xb1,
      (uint8_t )0x6a,
      (uint8_t )0xed,
      (uint8_t )0xf5,
      (uint8_t )0xaa,
      (uint8_t )0x0d,
      (uint8_t )0xe6,
      (uint8_t )0x57,
      (uint8_t )0xba,
      (uint8_t )0x63,
      (uint8_t )0x7b,
      (uint8_t )0x39,
      (uint8_t )0x1a,
      (uint8_t )0xaf,
      (uint8_t )0xd2,
      (uint8_t )0x55
    };
  uint8_t
  iv2[12] =
    {
      (uint8_t )0xca,
      (uint8_t )0xfe,
      (uint8_t )0xba,
      (uint8_t )0xbe,
      (uint8_t )0xfa,
      (uint8_t )0xce,
      (uint8_t )0xdb,
      (uint8_t )0xad,
      (uint8_t )0xde,
      (uint8_t )0xca,
      (uint8_t )0xf8,
      (uint8_t )0x88
    };
  uint32_t aadlen2 = (uint32_t )0;
  uint8_t aad2[aadlen2];
  memset(aad2, 0, aadlen2 * sizeof aad2[0]);
  uint8_t
  cipher2[80] =
    {
      (uint8_t )0x52,
      (uint8_t )0x2d,
      (uint8_t )0xc1,
      (uint8_t )0xf0,
      (uint8_t )0x99,
      (uint8_t )0x56,
      (uint8_t )0x7d,
      (uint8_t )0x07,
      (uint8_t )0xf4,
      (uint8_t )0x7f,
      (uint8_t )0x37,
      (uint8_t )0xa3,
      (uint8_t )0x2a,
      (uint8_t )0x84,
      (uint8_t )0x42,
      (uint8_t )0x7d,
      (uint8_t )0x64,
      (uint8_t )0x3a,
      (uint8_t )0x8c,
      (uint8_t )0xdc,
      (uint8_t )0xbf,
      (uint8_t )0xe5,
      (uint8_t )0xc0,
      (uint8_t )0xc9,
      (uint8_t )0x75,
      (uint8_t )0x98,
      (uint8_t )0xa2,
      (uint8_t )0xbd,
      (uint8_t )0x25,
      (uint8_t )0x55,
      (uint8_t )0xd1,
      (uint8_t )0xaa,
      (uint8_t )0x8c,
      (uint8_t )0xb0,
      (uint8_t )0x8e,
      (uint8_t )0x48,
      (uint8_t )0x59,
      (uint8_t )0x0d,
      (uint8_t )0xbb,
      (uint8_t )0x3d,
      (uint8_t )0xa7,
      (uint8_t )0xb0,
      (uint8_t )0x8b,
      (uint8_t )0x10,
      (uint8_t )0x56,
      (uint8_t )0x82,
      (uint8_t )0x88,
      (uint8_t )0x38,
      (uint8_t )0xc5,
      (uint8_t )0xf6,
      (uint8_t )0x1e,
      (uint8_t )0x63,
      (uint8_t )0x93,
      (uint8_t )0xba,
      (uint8_t )0x7a,
      (uint8_t )0x0a,
      (uint8_t )0xbc,
      (uint8_t )0xc9,
      (uint8_t )0xf6,
      (uint8_t )0x62,
      (uint8_t )0x89,
      (uint8_t )0x80,
      (uint8_t )0x15,
      (uint8_t )0xad,
      (uint8_t )0xb0,
      (uint8_t )0x94,
      (uint8_t )0xda,
      (uint8_t )0xc5,
      (uint8_t )0xd9,
      (uint8_t )0x34,
      (uint8_t )0x71,
      (uint8_t )0xbd,
      (uint8_t )0xec,
      (uint8_t )0x1a,
      (uint8_t )0x50,
      (uint8_t )0x22,
      (uint8_t )0x70,
      (uint8_t )0xe3,
      (uint8_t )0xcc,
      (uint8_t )0x6c
    };
  bool
  uu____15457 =
    test_aes_gcm(i1,
      (uint32_t )3,
      k2,
      iv2,
      aadlen2,
      aad2,
      plainlen2,
      plain2,
      cipher2);
  Crypto_Indexing_id i2 = Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_AES_256_GCM);
  uint8_t
  k3[32] =
    {
      (uint8_t )0xfe,
      (uint8_t )0xff,
      (uint8_t )0xe9,
      (uint8_t )0x92,
      (uint8_t )0x86,
      (uint8_t )0x65,
      (uint8_t )0x73,
      (uint8_t )0x1c,
      (uint8_t )0x6d,
      (uint8_t )0x6a,
      (uint8_t )0x8f,
      (uint8_t )0x94,
      (uint8_t )0x67,
      (uint8_t )0x30,
      (uint8_t )0x83,
      (uint8_t )0x08,
      (uint8_t )0xfe,
      (uint8_t )0xff,
      (uint8_t )0xe9,
      (uint8_t )0x92,
      (uint8_t )0x86,
      (uint8_t )0x65,
      (uint8_t )0x73,
      (uint8_t )0x1c,
      (uint8_t )0x6d,
      (uint8_t )0x6a,
      (uint8_t )0x8f,
      (uint8_t )0x94,
      (uint8_t )0x67,
      (uint8_t )0x30,
      (uint8_t )0x83,
      (uint8_t )0x08
    };
  uint32_t plainlen3 = (uint32_t )60;
  uint8_t
  plain3[60] =
    {
      (uint8_t )0xd9,
      (uint8_t )0x31,
      (uint8_t )0x32,
      (uint8_t )0x25,
      (uint8_t )0xf8,
      (uint8_t )0x84,
      (uint8_t )0x06,
      (uint8_t )0xe5,
      (uint8_t )0xa5,
      (uint8_t )0x59,
      (uint8_t )0x09,
      (uint8_t )0xc5,
      (uint8_t )0xaf,
      (uint8_t )0xf5,
      (uint8_t )0x26,
      (uint8_t )0x9a,
      (uint8_t )0x86,
      (uint8_t )0xa7,
      (uint8_t )0xa9,
      (uint8_t )0x53,
      (uint8_t )0x15,
      (uint8_t )0x34,
      (uint8_t )0xf7,
      (uint8_t )0xda,
      (uint8_t )0x2e,
      (uint8_t )0x4c,
      (uint8_t )0x30,
      (uint8_t )0x3d,
      (uint8_t )0x8a,
      (uint8_t )0x31,
      (uint8_t )0x8a,
      (uint8_t )0x72,
      (uint8_t )0x1c,
      (uint8_t )0x3c,
      (uint8_t )0x0c,
      (uint8_t )0x95,
      (uint8_t )0x95,
      (uint8_t )0x68,
      (uint8_t )0x09,
      (uint8_t )0x53,
      (uint8_t )0x2f,
      (uint8_t )0xcf,
      (uint8_t )0x0e,
      (uint8_t )0x24,
      (uint8_t )0x49,
      (uint8_t )0xa6,
      (uint8_t )0xb5,
      (uint8_t )0x25,
      (uint8_t )0xb1,
      (uint8_t )0x6a,
      (uint8_t )0xed,
      (uint8_t )0xf5,
      (uint8_t )0xaa,
      (uint8_t )0x0d,
      (uint8_t )0xe6,
      (uint8_t )0x57,
      (uint8_t )0xba,
      (uint8_t )0x63,
      (uint8_t )0x7b,
      (uint8_t )0x39
    };
  uint8_t
  iv3[12] =
    {
      (uint8_t )0xca,
      (uint8_t )0xfe,
      (uint8_t )0xba,
      (uint8_t )0xbe,
      (uint8_t )0xfa,
      (uint8_t )0xce,
      (uint8_t )0xdb,
      (uint8_t )0xad,
      (uint8_t )0xde,
      (uint8_t )0xca,
      (uint8_t )0xf8,
      (uint8_t )0x88
    };
  uint32_t aadlen3 = (uint32_t )20;
  uint8_t
  aad3[20] =
    {
      (uint8_t )0xfe,
      (uint8_t )0xed,
      (uint8_t )0xfa,
      (uint8_t )0xce,
      (uint8_t )0xde,
      (uint8_t )0xad,
      (uint8_t )0xbe,
      (uint8_t )0xef,
      (uint8_t )0xfe,
      (uint8_t )0xed,
      (uint8_t )0xfa,
      (uint8_t )0xce,
      (uint8_t )0xde,
      (uint8_t )0xad,
      (uint8_t )0xbe,
      (uint8_t )0xef,
      (uint8_t )0xab,
      (uint8_t )0xad,
      (uint8_t )0xda,
      (uint8_t )0xd2
    };
  uint8_t
  cipher3[76] =
    {
      (uint8_t )0x52,
      (uint8_t )0x2d,
      (uint8_t )0xc1,
      (uint8_t )0xf0,
      (uint8_t )0x99,
      (uint8_t )0x56,
      (uint8_t )0x7d,
      (uint8_t )0x07,
      (uint8_t )0xf4,
      (uint8_t )0x7f,
      (uint8_t )0x37,
      (uint8_t )0xa3,
      (uint8_t )0x2a,
      (uint8_t )0x84,
      (uint8_t )0x42,
      (uint8_t )0x7d,
      (uint8_t )0x64,
      (uint8_t )0x3a,
      (uint8_t )0x8c,
      (uint8_t )0xdc,
      (uint8_t )0xbf,
      (uint8_t )0xe5,
      (uint8_t )0xc0,
      (uint8_t )0xc9,
      (uint8_t )0x75,
      (uint8_t )0x98,
      (uint8_t )0xa2,
      (uint8_t )0xbd,
      (uint8_t )0x25,
      (uint8_t )0x55,
      (uint8_t )0xd1,
      (uint8_t )0xaa,
      (uint8_t )0x8c,
      (uint8_t )0xb0,
      (uint8_t )0x8e,
      (uint8_t )0x48,
      (uint8_t )0x59,
      (uint8_t )0x0d,
      (uint8_t )0xbb,
      (uint8_t )0x3d,
      (uint8_t )0xa7,
      (uint8_t )0xb0,
      (uint8_t )0x8b,
      (uint8_t )0x10,
      (uint8_t )0x56,
      (uint8_t )0x82,
      (uint8_t )0x88,
      (uint8_t )0x38,
      (uint8_t )0xc5,
      (uint8_t )0xf6,
      (uint8_t )0x1e,
      (uint8_t )0x63,
      (uint8_t )0x93,
      (uint8_t )0xba,
      (uint8_t )0x7a,
      (uint8_t )0x0a,
      (uint8_t )0xbc,
      (uint8_t )0xc9,
      (uint8_t )0xf6,
      (uint8_t )0x62,
      (uint8_t )0x76,
      (uint8_t )0xfc,
      (uint8_t )0x6e,
      (uint8_t )0xce,
      (uint8_t )0x0f,
      (uint8_t )0x4e,
      (uint8_t )0x17,
      (uint8_t )0x68,
      (uint8_t )0xcd,
      (uint8_t )0xdf,
      (uint8_t )0x88,
      (uint8_t )0x53,
      (uint8_t )0xbb,
      (uint8_t )0x2d,
      (uint8_t )0x55,
      (uint8_t )0x1b
    };
  bool
  uu____15458 =
    test_aes_gcm(i2,
      (uint32_t )4,
      k3,
      iv3,
      aadlen3,
      aad3,
      plainlen3,
      plain3,
      cipher3);
  Crypto_Indexing_id i3 = Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_AES_128_GCM);
  uint8_t k4[16] = { 0 };
  uint32_t plainlen4 = (uint32_t )0;
  uint8_t plain4[plainlen4];
  memset(plain4, 0, plainlen4 * sizeof plain4[0]);
  uint8_t iv4[12] = { 0 };
  uint32_t aadlen4 = (uint32_t )0;
  uint8_t aad4[aadlen4];
  memset(aad4, 0, aadlen4 * sizeof aad4[0]);
  uint8_t
  cipher4[16] =
    {
      (uint8_t )0x58,
      (uint8_t )0xe2,
      (uint8_t )0xfc,
      (uint8_t )0xce,
      (uint8_t )0xfa,
      (uint8_t )0x7e,
      (uint8_t )0x30,
      (uint8_t )0x61,
      (uint8_t )0x36,
      (uint8_t )0x7f,
      (uint8_t )0x1d,
      (uint8_t )0x57,
      (uint8_t )0xa4,
      (uint8_t )0xe7,
      (uint8_t )0x45,
      (uint8_t )0x5a
    };
  bool
  uu____15459 =
    test_aes_gcm(i3,
      (uint32_t )1,
      k4,
      iv4,
      aadlen4,
      aad4,
      plainlen4,
      plain4,
      cipher4);
  Crypto_Indexing_id i4 = Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_AES_128_GCM);
  uint8_t k5[16] = { 0 };
  uint32_t plainlen5 = (uint32_t )16;
  uint8_t plain5[plainlen5];
  memset(plain5, 0, plainlen5 * sizeof plain5[0]);
  uint8_t iv5[12] = { 0 };
  uint32_t aadlen5 = (uint32_t )0;
  uint8_t aad5[aadlen5];
  memset(aad5, 0, aadlen5 * sizeof aad5[0]);
  uint8_t
  cipher5[32] =
    {
      (uint8_t )0x03,
      (uint8_t )0x88,
      (uint8_t )0xda,
      (uint8_t )0xce,
      (uint8_t )0x60,
      (uint8_t )0xb6,
      (uint8_t )0xa3,
      (uint8_t )0x92,
      (uint8_t )0xf3,
      (uint8_t )0x28,
      (uint8_t )0xc2,
      (uint8_t )0xb9,
      (uint8_t )0x71,
      (uint8_t )0xb2,
      (uint8_t )0xfe,
      (uint8_t )0x78,
      (uint8_t )0xab,
      (uint8_t )0x6e,
      (uint8_t )0x47,
      (uint8_t )0xd4,
      (uint8_t )0x2c,
      (uint8_t )0xec,
      (uint8_t )0x13,
      (uint8_t )0xbd,
      (uint8_t )0xf5,
      (uint8_t )0x3a,
      (uint8_t )0x67,
      (uint8_t )0xb2,
      (uint8_t )0x12,
      (uint8_t )0x57,
      (uint8_t )0xbd,
      (uint8_t )0xdf
    };
  bool
  uu____15460 =
    test_aes_gcm(i4,
      (uint32_t )2,
      k5,
      iv5,
      aadlen5,
      aad5,
      plainlen5,
      plain5,
      cipher5);
  Crypto_Indexing_id i5 = Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_AES_128_GCM);
  uint8_t
  k6[16] =
    {
      (uint8_t )0xfe,
      (uint8_t )0xff,
      (uint8_t )0xe9,
      (uint8_t )0x92,
      (uint8_t )0x86,
      (uint8_t )0x65,
      (uint8_t )0x73,
      (uint8_t )0x1c,
      (uint8_t )0x6d,
      (uint8_t )0x6a,
      (uint8_t )0x8f,
      (uint8_t )0x94,
      (uint8_t )0x67,
      (uint8_t )0x30,
      (uint8_t )0x83,
      (uint8_t )0x08
    };
  uint32_t plainlen6 = (uint32_t )64;
  uint8_t
  plain6[64] =
    {
      (uint8_t )0xd9,
      (uint8_t )0x31,
      (uint8_t )0x32,
      (uint8_t )0x25,
      (uint8_t )0xf8,
      (uint8_t )0x84,
      (uint8_t )0x06,
      (uint8_t )0xe5,
      (uint8_t )0xa5,
      (uint8_t )0x59,
      (uint8_t )0x09,
      (uint8_t )0xc5,
      (uint8_t )0xaf,
      (uint8_t )0xf5,
      (uint8_t )0x26,
      (uint8_t )0x9a,
      (uint8_t )0x86,
      (uint8_t )0xa7,
      (uint8_t )0xa9,
      (uint8_t )0x53,
      (uint8_t )0x15,
      (uint8_t )0x34,
      (uint8_t )0xf7,
      (uint8_t )0xda,
      (uint8_t )0x2e,
      (uint8_t )0x4c,
      (uint8_t )0x30,
      (uint8_t )0x3d,
      (uint8_t )0x8a,
      (uint8_t )0x31,
      (uint8_t )0x8a,
      (uint8_t )0x72,
      (uint8_t )0x1c,
      (uint8_t )0x3c,
      (uint8_t )0x0c,
      (uint8_t )0x95,
      (uint8_t )0x95,
      (uint8_t )0x68,
      (uint8_t )0x09,
      (uint8_t )0x53,
      (uint8_t )0x2f,
      (uint8_t )0xcf,
      (uint8_t )0x0e,
      (uint8_t )0x24,
      (uint8_t )0x49,
      (uint8_t )0xa6,
      (uint8_t )0xb5,
      (uint8_t )0x25,
      (uint8_t )0xb1,
      (uint8_t )0x6a,
      (uint8_t )0xed,
      (uint8_t )0xf5,
      (uint8_t )0xaa,
      (uint8_t )0x0d,
      (uint8_t )0xe6,
      (uint8_t )0x57,
      (uint8_t )0xba,
      (uint8_t )0x63,
      (uint8_t )0x7b,
      (uint8_t )0x39,
      (uint8_t )0x1a,
      (uint8_t )0xaf,
      (uint8_t )0xd2,
      (uint8_t )0x55
    };
  uint8_t
  iv6[12] =
    {
      (uint8_t )0xca,
      (uint8_t )0xfe,
      (uint8_t )0xba,
      (uint8_t )0xbe,
      (uint8_t )0xfa,
      (uint8_t )0xce,
      (uint8_t )0xdb,
      (uint8_t )0xad,
      (uint8_t )0xde,
      (uint8_t )0xca,
      (uint8_t )0xf8,
      (uint8_t )0x88
    };
  uint32_t aadlen6 = (uint32_t )0;
  uint8_t aad6[aadlen6];
  memset(aad6, 0, aadlen6 * sizeof aad6[0]);
  uint8_t
  cipher6[80] =
    {
      (uint8_t )0x42,
      (uint8_t )0x83,
      (uint8_t )0x1e,
      (uint8_t )0xc2,
      (uint8_t )0x21,
      (uint8_t )0x77,
      (uint8_t )0x74,
      (uint8_t )0x24,
      (uint8_t )0x4b,
      (uint8_t )0x72,
      (uint8_t )0x21,
      (uint8_t )0xb7,
      (uint8_t )0x84,
      (uint8_t )0xd0,
      (uint8_t )0xd4,
      (uint8_t )0x9c,
      (uint8_t )0xe3,
      (uint8_t )0xaa,
      (uint8_t )0x21,
      (uint8_t )0x2f,
      (uint8_t )0x2c,
      (uint8_t )0x02,
      (uint8_t )0xa4,
      (uint8_t )0xe0,
      (uint8_t )0x35,
      (uint8_t )0xc1,
      (uint8_t )0x7e,
      (uint8_t )0x23,
      (uint8_t )0x29,
      (uint8_t )0xac,
      (uint8_t )0xa1,
      (uint8_t )0x2e,
      (uint8_t )0x21,
      (uint8_t )0xd5,
      (uint8_t )0x14,
      (uint8_t )0xb2,
      (uint8_t )0x54,
      (uint8_t )0x66,
      (uint8_t )0x93,
      (uint8_t )0x1c,
      (uint8_t )0x7d,
      (uint8_t )0x8f,
      (uint8_t )0x6a,
      (uint8_t )0x5a,
      (uint8_t )0xac,
      (uint8_t )0x84,
      (uint8_t )0xaa,
      (uint8_t )0x05,
      (uint8_t )0x1b,
      (uint8_t )0xa3,
      (uint8_t )0x0b,
      (uint8_t )0x39,
      (uint8_t )0x6a,
      (uint8_t )0x0a,
      (uint8_t )0xac,
      (uint8_t )0x97,
      (uint8_t )0x3d,
      (uint8_t )0x58,
      (uint8_t )0xe0,
      (uint8_t )0x91,
      (uint8_t )0x47,
      (uint8_t )0x3f,
      (uint8_t )0x59,
      (uint8_t )0x85,
      (uint8_t )0x4d,
      (uint8_t )0x5c,
      (uint8_t )0x2a,
      (uint8_t )0xf3,
      (uint8_t )0x27,
      (uint8_t )0xcd,
      (uint8_t )0x64,
      (uint8_t )0xa6,
      (uint8_t )0x2c,
      (uint8_t )0xf3,
      (uint8_t )0x5a,
      (uint8_t )0xbd,
      (uint8_t )0x2b,
      (uint8_t )0xa6,
      (uint8_t )0xfa,
      (uint8_t )0xb4
    };
  bool
  uu____15461 =
    test_aes_gcm(i5,
      (uint32_t )3,
      k6,
      iv6,
      aadlen6,
      aad6,
      plainlen6,
      plain6,
      cipher6);
  Crypto_Indexing_id i6 = Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_AES_128_GCM);
  uint8_t
  k[16] =
    {
      (uint8_t )0xfe,
      (uint8_t )0xff,
      (uint8_t )0xe9,
      (uint8_t )0x92,
      (uint8_t )0x86,
      (uint8_t )0x65,
      (uint8_t )0x73,
      (uint8_t )0x1c,
      (uint8_t )0x6d,
      (uint8_t )0x6a,
      (uint8_t )0x8f,
      (uint8_t )0x94,
      (uint8_t )0x67,
      (uint8_t )0x30,
      (uint8_t )0x83,
      (uint8_t )0x08
    };
  uint32_t plainlen = (uint32_t )60;
  uint8_t
  plain[60] =
    {
      (uint8_t )0xd9,
      (uint8_t )0x31,
      (uint8_t )0x32,
      (uint8_t )0x25,
      (uint8_t )0xf8,
      (uint8_t )0x84,
      (uint8_t )0x06,
      (uint8_t )0xe5,
      (uint8_t )0xa5,
      (uint8_t )0x59,
      (uint8_t )0x09,
      (uint8_t )0xc5,
      (uint8_t )0xaf,
      (uint8_t )0xf5,
      (uint8_t )0x26,
      (uint8_t )0x9a,
      (uint8_t )0x86,
      (uint8_t )0xa7,
      (uint8_t )0xa9,
      (uint8_t )0x53,
      (uint8_t )0x15,
      (uint8_t )0x34,
      (uint8_t )0xf7,
      (uint8_t )0xda,
      (uint8_t )0x2e,
      (uint8_t )0x4c,
      (uint8_t )0x30,
      (uint8_t )0x3d,
      (uint8_t )0x8a,
      (uint8_t )0x31,
      (uint8_t )0x8a,
      (uint8_t )0x72,
      (uint8_t )0x1c,
      (uint8_t )0x3c,
      (uint8_t )0x0c,
      (uint8_t )0x95,
      (uint8_t )0x95,
      (uint8_t )0x68,
      (uint8_t )0x09,
      (uint8_t )0x53,
      (uint8_t )0x2f,
      (uint8_t )0xcf,
      (uint8_t )0x0e,
      (uint8_t )0x24,
      (uint8_t )0x49,
      (uint8_t )0xa6,
      (uint8_t )0xb5,
      (uint8_t )0x25,
      (uint8_t )0xb1,
      (uint8_t )0x6a,
      (uint8_t )0xed,
      (uint8_t )0xf5,
      (uint8_t )0xaa,
      (uint8_t )0x0d,
      (uint8_t )0xe6,
      (uint8_t )0x57,
      (uint8_t )0xba,
      (uint8_t )0x63,
      (uint8_t )0x7b,
      (uint8_t )0x39
    };
  uint8_t
  iv[12] =
    {
      (uint8_t )0xca,
      (uint8_t )0xfe,
      (uint8_t )0xba,
      (uint8_t )0xbe,
      (uint8_t )0xfa,
      (uint8_t )0xce,
      (uint8_t )0xdb,
      (uint8_t )0xad,
      (uint8_t )0xde,
      (uint8_t )0xca,
      (uint8_t )0xf8,
      (uint8_t )0x88
    };
  uint32_t aadlen = (uint32_t )20;
  uint8_t
  aad[20] =
    {
      (uint8_t )0xfe,
      (uint8_t )0xed,
      (uint8_t )0xfa,
      (uint8_t )0xce,
      (uint8_t )0xde,
      (uint8_t )0xad,
      (uint8_t )0xbe,
      (uint8_t )0xef,
      (uint8_t )0xfe,
      (uint8_t )0xed,
      (uint8_t )0xfa,
      (uint8_t )0xce,
      (uint8_t )0xde,
      (uint8_t )0xad,
      (uint8_t )0xbe,
      (uint8_t )0xef,
      (uint8_t )0xab,
      (uint8_t )0xad,
      (uint8_t )0xda,
      (uint8_t )0xd2
    };
  uint8_t
  cipher[76] =
    {
      (uint8_t )0x42,
      (uint8_t )0x83,
      (uint8_t )0x1e,
      (uint8_t )0xc2,
      (uint8_t )0x21,
      (uint8_t )0x77,
      (uint8_t )0x74,
      (uint8_t )0x24,
      (uint8_t )0x4b,
      (uint8_t )0x72,
      (uint8_t )0x21,
      (uint8_t )0xb7,
      (uint8_t )0x84,
      (uint8_t )0xd0,
      (uint8_t )0xd4,
      (uint8_t )0x9c,
      (uint8_t )0xe3,
      (uint8_t )0xaa,
      (uint8_t )0x21,
      (uint8_t )0x2f,
      (uint8_t )0x2c,
      (uint8_t )0x02,
      (uint8_t )0xa4,
      (uint8_t )0xe0,
      (uint8_t )0x35,
      (uint8_t )0xc1,
      (uint8_t )0x7e,
      (uint8_t )0x23,
      (uint8_t )0x29,
      (uint8_t )0xac,
      (uint8_t )0xa1,
      (uint8_t )0x2e,
      (uint8_t )0x21,
      (uint8_t )0xd5,
      (uint8_t )0x14,
      (uint8_t )0xb2,
      (uint8_t )0x54,
      (uint8_t )0x66,
      (uint8_t )0x93,
      (uint8_t )0x1c,
      (uint8_t )0x7d,
      (uint8_t )0x8f,
      (uint8_t )0x6a,
      (uint8_t )0x5a,
      (uint8_t )0xac,
      (uint8_t )0x84,
      (uint8_t )0xaa,
      (uint8_t )0x05,
      (uint8_t )0x1b,
      (uint8_t )0xa3,
      (uint8_t )0x0b,
      (uint8_t )0x39,
      (uint8_t )0x6a,
      (uint8_t )0x0a,
      (uint8_t )0xac,
      (uint8_t )0x97,
      (uint8_t )0x3d,
      (uint8_t )0x58,
      (uint8_t )0xe0,
      (uint8_t )0x91,
      (uint8_t )0x5b,
      (uint8_t )0xc9,
      (uint8_t )0x4f,
      (uint8_t )0xbc,
      (uint8_t )0x32,
      (uint8_t )0x21,
      (uint8_t )0xa5,
      (uint8_t )0xdb,
      (uint8_t )0x94,
      (uint8_t )0xfa,
      (uint8_t )0xe9,
      (uint8_t )0x5a,
      (uint8_t )0xe7,
      (uint8_t )0x12,
      (uint8_t )0x1a,
      (uint8_t )0x47
    };
  bool uu____15462 = test_aes_gcm(i6, (uint32_t )4, k, iv, aadlen, aad, plainlen, plain, cipher);
  return exit_success;
}

