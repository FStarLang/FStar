#include "testlib.h"
#include <time.h>
#include "testutils.h"
#include "Crypto_AEAD.h"
#include "Crypto_AEAD_Encrypt.h"
#include "Crypto_AEAD_Wrappers_CMA.h"
#include <openssl/evp.h>

#define PLAINLEN (16*1024)
#define AADLEN (12)
#define NONCELEN 24
#define KEYLEN 32
#define IVLEN 12

uint8_t nonce[NONCELEN] = {
  0x00, 0x01, 0x02, 0x03,
  0x04, 0x05, 0x06, 0x07,
  0x08, 0x09, 0x10, 0x11,
  0x12, 0x13, 0x14, 0x15,
  0x16, 0x17, 0x18, 0x19,
  0x20, 0x21, 0x22, 0x23,
};

uint8_t key[KEYLEN] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1b
};

uint8_t sk[KEYLEN] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1c
};

uint8_t aad[AADLEN] = {
  0x50, 0x51, 0x52, 0x53,
  0xc0, 0xc1, 0xc2, 0xc3,
  0xc4, 0xc5, 0xc6, 0xc7
};

uint8_t ivBuffer[IVLEN] = {
  0x07, 0x00, 0x00, 0x00,
  0x40, 0x41, 0x42, 0x43,
  0x44, 0x45, 0x46, 0x47
};

#define ROUNDS 1000
#define AES_ROUNDS 1

#define AES_GCM 0
#define CHACHA_POLY 1

void print_results(char *txt, double t1, unsigned long long d1, int rounds, int plainlen){
  printf("Testing: %s\n", txt);
  printf("Cycles for %d 2^14 bytes: %llu (%.2fcycles/byte)\n", rounds, d1, (double)d1/plainlen/rounds);
  printf("User time for %d 2^14 bytes: %f (%fns/byte)\n", rounds, t1, t1*1000000/plainlen/rounds);
}

int openssl_aead_encrypt(unsigned char *plaintext, int plaintext_len, unsigned char *aad,
                         int aad_len, unsigned char *key, unsigned char *iv,
                         unsigned char *ciphertext, unsigned char *tag, int cipher){
  EVP_CIPHER_CTX *ctx;
  int len;
  int ciphertext_len;
  /* Create and initialise the context */
  if(!(ctx = EVP_CIPHER_CTX_new())) return EXIT_FAILURE;
  /* Initialise the encryption operation. */
  if (cipher == AES_GCM) {
    if(1 != EVP_EncryptInit_ex(ctx, EVP_aes_256_gcm(), NULL, NULL, NULL))
      return EXIT_FAILURE;
  } else {
    if(1 != EVP_EncryptInit_ex(ctx, EVP_chacha20_poly1305(), NULL, NULL, NULL))
      return EXIT_FAILURE;
  }

  clock_t c1, c2;
  double t1, t2;
  unsigned long long a,b,d1,d2;
  c1 = clock();
  a = rdtsc();
  for (int j = 0; j < ROUNDS; j++){
    /* Set IV length if default 12 bytes (96 bits) is not appropriate */
    if(1 != EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, 16, NULL))
      return EXIT_FAILURE;
    /* Initialise key and IV */
    if(1 != EVP_EncryptInit_ex(ctx, NULL, NULL, key, iv)) return EXIT_FAILURE;
    /* Provide any AAD data. This can be called zero or more times as
     * required
     */
    if(1 != EVP_EncryptUpdate(ctx, NULL, &len, aad, aad_len))
      return EXIT_FAILURE;
    /* Provide the message to be encrypted, and obtain the encrypted output.
     * EVP_EncryptUpdate can be called multiple times if necessary
     */
    if(1 != EVP_EncryptUpdate(ctx, ciphertext, &len, plaintext, plaintext_len))
      return EXIT_FAILURE;
    ciphertext_len = len;
    /* Finalise the encryption. Normally ciphertext bytes may be written at
     * this stage, but this does not occur in GCM mode
     */
    if(1 != EVP_EncryptFinal_ex(ctx, ciphertext + len, &len)) return EXIT_FAILURE;
    ciphertext_len += len;
    /* Get the tag */
    if(1 != EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_GET_TAG, 16, tag))
      return EXIT_FAILURE;
  }
  b = rdtsc();
  c2 = clock();
  d1 = b - a;
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  print_results(cipher == AES_GCM ? "openssl-aes-256-gcm" : "openssl-chacha20-poly1305", t1, d1, ROUNDS, PLAINLEN);
  EVP_CIPHER_CTX_free(ctx);
  return ciphertext_len;
}


void test_kremlin_aead(void *plain, void*cipher, int alg){
  clock_t c1, c2;
  double t1, t2;

  FStar_UInt128_t iv = Crypto_Symmetric_Bytes_load_uint128((uint32_t )12, ivBuffer);
  Crypto_Indexing_id i = alg == AES_GCM ? Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_AES_256_GCM) : Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_CHACHA20_POLY1305);
  unsigned long long a,b,d1,d2;
  FStar_HyperHeap_rid mac_rgn = FStar_ST_new_region(FStar_HyperHeap_root);
  uint8_t *key_p = calloc(Crypto_Symmetric_PRF_keylen(i), sizeof (uint8_t ));
  memcpy(key_p, key, Crypto_Symmetric_PRF_keylen(i) * sizeof key[0]);
  Crypto_Symmetric_PRF_state____
  prf =
    {
      .rgn = FStar_HyperHeap_root,
      .mac_rgn = mac_rgn,
      .key = key_p,
      .table = (Crypto_Symmetric_PRF_no_table(i, FStar_HyperHeap_root, mac_rgn) , (void *)0)
    };
  void *log = FStar_ST_ralloc(FStar_HyperHeap_root, FStar_Seq_createEmpty((uint8_t )0));
  FStar_Pervasives_option__uint8_t_ ak;
  if (Crypto_Symmetric_UF1CMA_skeyed(i))
  {
    Crypto_Symmetric_PRF_domain____ x = { .iv = Crypto_Symmetric_PRF_iv_0, .ctr = (uint32_t )0 };
    uint8_t *keyBuffer = calloc(Crypto_Symmetric_UF1CMA_skeylen(i), sizeof (uint8_t ));
    Crypto_Symmetric_PRF_getBlock(i, prf, x, Crypto_Symmetric_UF1CMA_skeylen(i), keyBuffer);
    ak =
      (FStar_Pervasives_option__uint8_t_ ){
        .tag = FStar_Pervasives_option__uint8_t__Some,
        { .case_Some = { .v = keyBuffer } }
      };
  }
  else
    ak = (FStar_Pervasives_option__uint8_t_ ){ .tag = FStar_Pervasives_option__uint8_t__None };
  Crypto_AEAD_Invariant_aead_state_______
  st0 = { .log_region = FStar_HyperHeap_root, .log = log, .prf = prf, .ak = ak };

  c1 = clock();
  a = rdtsc();
  int rounds = alg == AES_GCM ? 10 : ROUNDS;
  for (int j = 0; j < rounds; j++) Crypto_AEAD_Encrypt_encrypt(i, st0, iv, AADLEN, aad, PLAINLEN, plain, cipher);
  b = rdtsc();
  c2 = clock();
  d1 = b - a;
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  print_results(alg == AES_GCM ? "Kremlin-C-aes256-gcm" : "Kremlin-C-chacha20-poly1305", t1, d1, rounds, PLAINLEN);
}

void test_kremlin_prf(void *plain, void*cipher, int alg){
  clock_t c1, c2;
  double t1, t2;

  FStar_UInt128_t iv = Crypto_Symmetric_Bytes_load_uint128((uint32_t )12, ivBuffer);
  Crypto_Indexing_id i = alg == AES_GCM ? Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_AES_256_GCM) : Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_CHACHA20_POLY1305);
  unsigned long long a,b,d1,d2;
  FStar_HyperHeap_rid mac_rgn = FStar_ST_new_region(FStar_HyperHeap_root);
  uint8_t *key_p = calloc(Crypto_Symmetric_PRF_keylen(i), sizeof (uint8_t ));
  memcpy(key_p, key, Crypto_Symmetric_PRF_keylen(i) * sizeof key[0]);
  Crypto_Symmetric_PRF_state____
  prf =
    {
      .rgn = FStar_HyperHeap_root,
      .mac_rgn = mac_rgn,
      .key = key_p,
      .table = (Crypto_Symmetric_PRF_no_table(i, FStar_HyperHeap_root, mac_rgn) , (void *)0)
    };
  void *log = FStar_ST_ralloc(FStar_HyperHeap_root, FStar_Seq_createEmpty((uint8_t )0));
  FStar_Pervasives_option__uint8_t_ ak;
  if (Crypto_Symmetric_UF1CMA_skeyed(i))
  {
    Crypto_Symmetric_PRF_domain____ x = { .iv = Crypto_Symmetric_PRF_iv_0, .ctr = (uint32_t )0 };
    uint8_t *keyBuffer = calloc(Crypto_Symmetric_UF1CMA_skeylen(i), sizeof (uint8_t ));
    Crypto_Symmetric_PRF_getBlock(i, prf, x, Crypto_Symmetric_UF1CMA_skeylen(i), keyBuffer);
    ak =
      (FStar_Pervasives_option__uint8_t_ ){
        .tag = FStar_Pervasives_option__uint8_t__Some,
        { .case_Some = { .v = keyBuffer } }
      };
  }
  else
    ak = (FStar_Pervasives_option__uint8_t_ ){ .tag = FStar_Pervasives_option__uint8_t__None };
  Crypto_AEAD_Invariant_aead_state_______
  st0 = { .log_region = FStar_HyperHeap_root, .log = log, .prf = prf, .ak = ak };
  FStar_HyperStack_mem h1 = (void *)(uint8_t )0;
  Crypto_Symmetric_PRF_domain____ x = { .iv = Crypto_Symmetric_PRF_iv_0, .ctr = (uint32_t )0 };
  c1 = clock();
  a = rdtsc();
  int rounds = alg == AES_GCM ? AES_ROUNDS : ROUNDS;
  for (int j = 0; j < rounds; j++) Crypto_AEAD_EnxorDexor_counter_enxor(i,
                                                             Crypto_AEAD_Invariant___proj__AEADState__item__prf(i, Crypto_Indexing_rw_Writer, st0),
                                                             x,
                                                             PLAINLEN,
                                                             PLAINLEN,
                                                             plain,
                                                             cipher,
                                                             h1);
  b = rdtsc();
  c2 = clock();
  d1 = b - a;
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  print_results(alg == AES_GCM ? "Kremlin-C-aes256" : "Kremlin-C-chacha20", t1, d1, rounds, PLAINLEN);
}


void test_kremlin_mac(void *plain, void*cipher, int alg){
  clock_t c1, c2;
  double t1, t2;
  uint8_t tag[16];

  FStar_UInt128_t iv = Crypto_Symmetric_Bytes_load_uint128((uint32_t )12, ivBuffer);
  Crypto_Indexing_id i = alg == AES_GCM ? Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_AES_256_GCM) : Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_CHACHA20_POLY1305);
  unsigned long long a,b,d1,d2;
  FStar_HyperHeap_rid mac_rgn = FStar_ST_new_region(FStar_HyperHeap_root);
  uint8_t *key_p = calloc(Crypto_Symmetric_PRF_keylen(i), sizeof (uint8_t ));
  memcpy(key_p, key, Crypto_Symmetric_PRF_keylen(i) * sizeof key[0]);
  Crypto_Symmetric_PRF_state____
  prf =
    {
      .rgn = FStar_HyperHeap_root,
      .mac_rgn = mac_rgn,
      .key = key_p,
      .table = (Crypto_Symmetric_PRF_no_table(i, FStar_HyperHeap_root, mac_rgn) , (void *)0)
    };
  void *log = FStar_ST_ralloc(FStar_HyperHeap_root, FStar_Seq_createEmpty((uint8_t )0));
  FStar_Pervasives_option__uint8_t_ ak;
  if (Crypto_Symmetric_UF1CMA_skeyed(i))
  {
    Crypto_Symmetric_PRF_domain____ x = { .iv = Crypto_Symmetric_PRF_iv_0, .ctr = (uint32_t )0 };
    uint8_t *keyBuffer = calloc(Crypto_Symmetric_UF1CMA_skeylen(i), sizeof (uint8_t ));
    Crypto_Symmetric_PRF_getBlock(i, prf, x, Crypto_Symmetric_UF1CMA_skeylen(i), keyBuffer);
    ak =
      (FStar_Pervasives_option__uint8_t_ ){
        .tag = FStar_Pervasives_option__uint8_t__Some,
        { .case_Some = { .v = keyBuffer } }
      };
  }
  else
    ak = (FStar_Pervasives_option__uint8_t_ ){ .tag = FStar_Pervasives_option__uint8_t__None };
  Crypto_AEAD_Invariant_aead_state_______
  st0 = { .log_region = FStar_HyperHeap_root, .log = log, .prf = prf, .ak = ak };
  FStar_HyperStack_mem h1 = (void *)(uint8_t )0;
  Crypto_Symmetric_PRF_domain____ x = { .iv = Crypto_Symmetric_PRF_iv_0, .ctr = (uint32_t )0 };
  c1 = clock();
  a = rdtsc();
  int rounds = alg == AES_GCM ? AES_ROUNDS : ROUNDS;

  uint64_t buf0[5], buf00[5];
  uint8_t buf[16], buff[16];
  K___Crypto_Indexing_id_FStar_UInt128_t macId = { .fst = i, .snd = x.iv };

  /**/
  uint8_t *keyBuffer = calloc(Crypto_Symmetric_UF1CMA_keylen(i), sizeof (uint8_t ));
  Crypto_Symmetric_MAC__buffer r;
  switch (Crypto_Symmetric_MAC_alg(macId))
  {
    case Crypto_Indexing_macAlg_POLY1305:
      {
        uint64_t *buf = calloc((uint32_t )5, sizeof (uint64_t ));
        r =
          (Crypto_Symmetric_MAC__buffer ){
            .tag = Crypto_Symmetric_MAC__buffer_B_POLY1305,
            { .case_B_POLY1305 = { ._0 = buf } }
          };
        break;
      }
    case Crypto_Indexing_macAlg_GHASH:
      {
        uint8_t *buf = calloc(Crypto_Symmetric_MAC_wlen, sizeof (uint8_t ));
        r =
          (Crypto_Symmetric_MAC__buffer ){
            .tag = Crypto_Symmetric_MAC__buffer_B_GHASH,
            { .case_B_GHASH = { ._0 = buf } }
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
  bool scrut0 = Crypto_Symmetric_UF1CMA_skeyed(FStar_Pervasives_fst(macId));
  K___uint8_t__uint8_t_ scrut;
  if (scrut0 == true)
    scrut =
      (K___uint8_t__uint8_t_ ){
        .fst
        =
        Crypto_Symmetric_UF1CMA_get_skey(Crypto_Symmetric_PRF___proj__State__item__mac_rgn(i,
            Crypto_AEAD_Invariant___proj__AEADState__item__prf(i, Crypto_Indexing_rw_Writer, st0)),
          FStar_Pervasives_fst(macId),
          Crypto_AEAD_Invariant___proj__AEADState__item__ak(i, Crypto_Indexing_rw_Writer, st0)),
        .snd = keyBuffer
      };
  else
  {
    bool uu____4410 = scrut0;
    scrut =
      (K___uint8_t__uint8_t_ ){ .fst = keyBuffer + (uint32_t )0, .snd = keyBuffer + (uint32_t )16 };
  }
  uint8_t *rb = scrut.fst;
  uint8_t *sb = scrut.snd;
  Crypto_Symmetric_MAC_encode_r(macId, r, rb);
  memcpy(s, sb, (uint32_t )16 * sizeof sb[0]);
  /**/

  Crypto_Symmetric_UF1CMA_state____
  ak2 =
    {
      .region
      =
      Crypto_Symmetric_PRF___proj__State__item__mac_rgn(i,
        Crypto_AEAD_Invariant___proj__AEADState__item__prf(i, Crypto_Indexing_rw_Writer, st0)),
      .r = r,
      .s = s,
      .log = (uint8_t )0
    };

  for (int j = 0; j < rounds; j++){

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
            { .case_B_POLY1305 = { ._0 = buf0 } }
          };
          break;
        }
      case Crypto_Indexing_macAlg_GHASH:
        {
          memset(buf, 0, (uint32_t )16 * sizeof buf[0]);
          a =
            (Crypto_Symmetric_MAC__buffer ){
            .tag = Crypto_Symmetric_MAC__buffer_B_GHASH,
            { .case_B_GHASH = { ._0 = buf } }
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
    Crypto_Symmetric_UF1CMA_accBuffer____ acc = { .a = a, .l = (uint8_t )0 };
    Crypto_AEAD_Encoding_add_bytes((K___Crypto_Indexing_id_FStar_UInt128_t ){
        .fst = i,
          .snd = x.iv
          },
      ak2,
      acc,
      AADLEN,
      aad);
    Crypto_AEAD_Encoding_add_bytes((K___Crypto_Indexing_id_FStar_UInt128_t ){
        .fst = i,
          .snd = x.iv
          },
      ak2,
      acc,
      PLAINLEN,
      cipher);
    uint8_t final_word[16] = { 0 };
    Crypto_Indexing_id
      id = ((K___Crypto_Indexing_id_FStar_UInt128_t ){ .fst = i, .snd = x.iv }).fst;
    switch (Crypto_Indexing_macAlg_of_id(id))
      {
      case Crypto_Indexing_macAlg_POLY1305:
        {
          Crypto_Symmetric_Bytes_store_uint32((uint32_t )4, final_word + (uint32_t )0, AADLEN);
          Crypto_Symmetric_Bytes_store_uint32((uint32_t )4, final_word + (uint32_t )8, PLAINLEN);
          break;
        }
      case Crypto_Indexing_macAlg_GHASH:
        {
          Crypto_Symmetric_Bytes_store_big32((uint32_t )4,
                                             final_word + (uint32_t )4,
                                             AADLEN * (uint32_t )8);
          Crypto_Symmetric_Bytes_store_big32((uint32_t )4,
                                             final_word + (uint32_t )12,
                                             PLAINLEN * (uint32_t )8);
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
      ak2,
      acc,
      final_word);
    Crypto_Symmetric_UF1CMA_accBuffer____ acc0 = acc;
    Crypto_Symmetric_UF1CMA_accBuffer____ acc1 = acc0;
    FStar_HyperStack_mem h3 = (void *)(uint8_t )0;
    Crypto_AEAD_Wrappers_CMA_mac_wrapper((K___Crypto_Indexing_id_FStar_UInt128_t ){ .fst = i, .snd = x.iv },
                            ak2,
                            acc1,
                            tag);
  }

  b = rdtsc();
  c2 = clock();
  d1 = b - a;
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  print_results(alg == AES_GCM ? "Kremlin-C-gcm" : "Kremlin-C-poly1305", t1, d1, rounds, PLAINLEN);
}

void test_crypto_aead(){
  void *plain = malloc(PLAINLEN), *cipher = malloc(PLAINLEN+16);
  uint8_t mac[16];
  test_kremlin_aead(plain, cipher, AES_GCM);
  test_kremlin_aead(plain, cipher, CHACHA_POLY);
  openssl_aead_encrypt(plain, PLAINLEN, aad, AADLEN, key, ivBuffer, cipher, mac, AES_GCM);
  openssl_aead_encrypt(plain, PLAINLEN, aad, AADLEN, key, ivBuffer, cipher, mac, CHACHA_POLY);
  test_kremlin_prf(plain, cipher, AES_GCM);
  test_kremlin_prf(plain, cipher, CHACHA_POLY);
  test_kremlin_mac(plain, cipher, AES_GCM);
  test_kremlin_mac(plain, cipher, CHACHA_POLY);
}


int main(){
  test_crypto_aead();
  return EXIT_SUCCESS;
}
