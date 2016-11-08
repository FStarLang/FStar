#include "testlib.h"
#include <time.h>
#include "testutils.h"
#include "Crypto_AEAD.h"
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

#define AES_GCM 0
#define CHACHA_POLY 1

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
  printf("[openssl-%s] No of cycles for %d 2^14 bytes AEAD blocks: %llu (%llucycles/byte)\n", cipher==AES_GCM ? "aes-gcm" : "chacha-poly", ROUNDS, d1, d1/PLAINLEN/ROUNDS);
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  printf("[openssl-%s] User time for %d 2^14 bytes AEAD blocks: %f (%fns/byte)\n", cipher==AES_GCM ? "aes-gcm" : "chacha-poly", ROUNDS, t1, t1*1000000/PLAINLEN/ROUNDS);
  /* Clean up */
  EVP_CIPHER_CTX_free(ctx);
  return ciphertext_len;
}


void test_crypto_aead(){
  void *plain = malloc(PLAINLEN), *cipher = malloc(PLAINLEN+16);
  uint8_t mac[16];
  clock_t c1, c2;
  double t1, t2;

  FStar_UInt128_t iv = Crypto_Symmetric_Bytes_load_uint128((uint32_t )12, ivBuffer);
  Crypto_Indexing_id i = Crypto_Indexing_testId(Crypto_Indexing_aeadAlg_CHACHA20_POLY1305);
  unsigned long long a,b,d1,d2;
  FStar_HyperHeap_rid mac_rgn = FStar_ST_new_region(FStar_HyperHeap_root);
  uint8_t *key_p = calloc(Crypto_Symmetric_PRF_keylen(i), sizeof (uint8_t ));
  memcpy(key_p, key, Crypto_Symmetric_PRF_keylen(i) * sizeof key[0]);
  Crypto_Symmetric_PRF_state____
  prf =
    {
      .x00 = FStar_HyperHeap_root,
      .x01 = mac_rgn,
      .x02 = key_p,
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

  c1 = clock();
  a = rdtsc();
  for (int j = 0; j < ROUNDS; j++) Crypto_AEAD_encrypt(i, st0, iv, AADLEN, aad, PLAINLEN, plain, cipher);
  b = rdtsc();
  c2 = clock();
  d1 = b - a;
  printf("No of cycles for %d 2^14 bytes AEAD blocks: %llu (%llucycles/byte)\n", ROUNDS, d1, d1/PLAINLEN/ROUNDS);
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  printf("User time for %d 2^14 bytes AEAD blocks: %f (%fns/byte)\n", ROUNDS, t1, t1*1000000/PLAINLEN/ROUNDS);

  openssl_aead_encrypt(plain, PLAINLEN, aad, AADLEN, key, ivBuffer, cipher, mac, AES_GCM);
  openssl_aead_encrypt(plain, PLAINLEN, aad, AADLEN, key, ivBuffer, cipher, mac, CHACHA_POLY);

}


int main(){
  test_crypto_aead();
  return EXIT_SUCCESS;
}
