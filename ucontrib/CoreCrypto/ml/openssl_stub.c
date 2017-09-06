/* -------------------------------------------------------------------- */
#include <sys/types.h>
#include <sys/stat.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include <caml/alloc.h>
#include <caml/callback.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

#include <openssl/conf.h>
#include <openssl/err.h>
#include <openssl/bn.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>
#include <openssl/dsa.h>
#include <openssl/dh.h>
#include <openssl/pem.h>
#include <openssl/ec.h>
#include <openssl/objects.h>
#include <openssl/obj_mac.h>

/* -------------------------------------------------------------------- */
static value Val_some(value mlvalue) {
    CAMLparam1(mlvalue);
    CAMLlocal1(aout);

    aout = caml_alloc(1, 0);
    Store_field(aout, 0, mlvalue);

    CAMLreturn(aout);
}

#define Val_none Val_int(0)
#define Some_val(v) Field(v,0)

static uint8_t* buffer_of_platform_bytes(value mlbytes, size_t* out_length) {
  *out_length = caml_string_length(mlbytes);
  uint8_t *buf = (uint8_t*)malloc(*out_length);
  memcpy(buf, String_val(mlbytes), *out_length);
  return buf;
}

/* -------------------------------------------------------------------- */

CAMLprim value ocaml_openssl_init(value unit) {
  CAMLparam1(unit);
  OPENSSL_init_crypto(OPENSSL_INIT_LOAD_CRYPTO_STRINGS | OPENSSL_INIT_ADD_ALL_CIPHERS | OPENSSL_INIT_ADD_ALL_DIGESTS, NULL);
  CONF_modules_load(NULL, "CoreCrypto", 0);
  RAND_poll();
  CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
#define MD_val(v) (*((const EVP_MD**) Data_custom_val(v)))

static struct custom_operations evp_md_ops = {
  .identifier  = "ocaml_evp_md",
  .finalize    = custom_finalize_default,
  .compare     = custom_compare_default,
  .hash        = custom_hash_default,
  .serialize   = custom_serialize_default,
  .deserialize = custom_deserialize_default,
};

/* -------------------------------------------------------------------- */
#define EVP_MD_GEN(X) \
  CAMLprim value ocaml_EVP_MD_##X(value unit) { \
      CAMLparam1(unit);                         \
      CAMLlocal1(aout);                         \
                                                \
      aout = caml_alloc_custom(&evp_md_ops, sizeof(EVP_MD*), 0, 1); \
      MD_val(aout) = EVP_##X();                 \
                                                \
      CAMLreturn(aout);                         \
  }

EVP_MD_GEN(md_null);
EVP_MD_GEN(md5);
EVP_MD_GEN(sha1);
EVP_MD_GEN(sha224);
EVP_MD_GEN(sha256);
EVP_MD_GEN(sha384);
EVP_MD_GEN(sha512);

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_MD_block_size(value md) {
    CAMLparam1(md);
    CAMLreturn(Val_int(EVP_MD_block_size(MD_val(md))));
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_MD_size(value md) {
    CAMLparam1(md);
    CAMLreturn(Val_int(EVP_MD_size(MD_val(md))));
}

/* -------------------------------------------------------------------- */
#define MD_CTX_val(v) (*((EVP_MD_CTX**) Data_custom_val(v)))

static void ocaml_evp_md_ctx_finalize(value mlctx) {
    EVP_MD_CTX *ctx = MD_CTX_val(mlctx);

    if (ctx != NULL)
        EVP_MD_CTX_free(ctx);
}

static struct custom_operations evp_md_ctx_ops = {
  .identifier  = "ocaml_evp_md_ctx",
  .finalize    = ocaml_evp_md_ctx_finalize,
  .compare     = custom_compare_default,
  .hash        = custom_hash_default,
  .serialize   = custom_serialize_default,
  .deserialize = custom_deserialize_default,
};

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_MD_CTX_new(value md) {
    EVP_MD_CTX *ctx = NULL;

    CAMLparam1(md);
    CAMLlocal1(mlctx);

    mlctx = caml_alloc_custom(&evp_md_ctx_ops, sizeof(EVP_MD_CTX*), 0, 1);

    if ((ctx = EVP_MD_CTX_new()) == NULL)
        caml_failwith("cannot alloc EVP_MD_CTX structure");

    if (EVP_DigestInit_ex(ctx, MD_val(md), NULL) == 0) {
        EVP_MD_CTX_free(ctx);
        caml_failwith("cannot initialize EVP_MD_CTX structure");
    }

    MD_CTX_val(mlctx) = ctx;
    CAMLreturn(mlctx);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_MD_CTX_fini(value mlctx) {
    EVP_MD_CTX *ctx = NULL;

    CAMLparam1(mlctx);

    if ((ctx = MD_CTX_val(mlctx)) != NULL) {
        EVP_MD_CTX_free(ctx);
        MD_CTX_val(mlctx) = NULL;
    }

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_MD_CTX_update(value mlctx, value mldata) {
    EVP_MD_CTX *ctx = NULL;

    CAMLparam2(mlctx, mldata);

    if ((ctx = MD_CTX_val(mlctx)) == NULL)
        caml_invalid_argument("MD_CTX has been disposed");

    EVP_DigestUpdate(ctx, String_val(mldata), caml_string_length(mldata));

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_MD_CTX_final(value mlctx) {
    EVP_MD_CTX *ctx = NULL;

    CAMLparam1(mlctx);
    CAMLlocal1(aout);

    if ((ctx = MD_CTX_val(mlctx)) == NULL)
        caml_invalid_argument("MD_CTX has been disposed");

    aout = caml_alloc_string(EVP_MD_CTX_size(ctx));
    (void) EVP_DigestFinal_ex(ctx, (uint8_t*) String_val(aout), NULL);
    EVP_MD_CTX_free(ctx);
    MD_CTX_val(mlctx) = NULL;

    CAMLreturn(aout);
}

/* -------------------------------------------------------------------- */
#define CIPHER_val(v) (*((const EVP_CIPHER**) Data_custom_val(v)))

static struct custom_operations evp_cipher_ops = {
  .identifier  = "ocaml_evp_cipher",
  .finalize    = custom_finalize_default,
  .compare     = custom_compare_default,
  .hash        = custom_hash_default,
  .serialize   = custom_serialize_default,
  .deserialize = custom_deserialize_default,
};

/* -------------------------------------------------------------------- */
#define EVP_CIPHER_GEN(X) \
  CAMLprim value ocaml_EVP_CIPHER_##X(value unit) { \
      CAMLparam1(unit);                             \
      CAMLlocal1(cipher);                           \
                                                    \
      cipher = caml_alloc_custom(&evp_cipher_ops, sizeof(EVP_CIPHER*), 0, 1); \
      CIPHER_val(cipher) = EVP_##X();               \
                                                    \
      CAMLreturn(cipher);                           \
  }

EVP_CIPHER_GEN(des_ede3);
EVP_CIPHER_GEN(des_ede3_cbc);
EVP_CIPHER_GEN(aes_128_ecb);
EVP_CIPHER_GEN(aes_128_cbc);
EVP_CIPHER_GEN(aes_256_ecb);
EVP_CIPHER_GEN(aes_256_cbc);
EVP_CIPHER_GEN(aes_128_gcm);
EVP_CIPHER_GEN(aes_256_gcm);
EVP_CIPHER_GEN(chacha20_poly1305);
EVP_CIPHER_GEN(rc4);

/* -------------------------------------------------------------------- */
#define CIPHER_CTX_val(v) (*((EVP_CIPHER_CTX**) Data_custom_val(v)))

static void ocaml_evp_cipher_finalize(value mlctx) {
    EVP_CIPHER_CTX *ctx = CIPHER_CTX_val(mlctx);

    if (ctx != NULL) {
        EVP_CIPHER_CTX_reset(ctx);
        EVP_CIPHER_CTX_free(ctx);
    }
}

static struct custom_operations evp_cipher_ctx_ops = {
  .identifier  = "ocaml_evp_cipher_ctx",
  .finalize    = ocaml_evp_cipher_finalize,
  .compare     = custom_compare_default,
  .hash        = custom_hash_default,
  .serialize   = custom_serialize_default,
  .deserialize = custom_deserialize_default,
};

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_create(value cipher, value forenc) {
    EVP_CIPHER_CTX *ctx = NULL;

    CAMLparam2(cipher, forenc);
    CAMLlocal1(mlctx);

    mlctx = caml_alloc_custom(&evp_cipher_ctx_ops, sizeof(EVP_CIPHER_CTX*), 0, 1);

    if ((ctx = EVP_CIPHER_CTX_new()) == NULL)
        caml_failwith("cannot alloc EVP_CIPHER_CTX structure");

    EVP_CIPHER_CTX_reset(ctx);

    // Set all parameters to NULL except the cipher type in this initial call
    // Give remaining parameters in subsequent calls (e.g. EVP_CIPHER_set_key),
    // all of which have cipher type set to NULL
    if (EVP_CipherInit_ex(ctx, CIPHER_val(cipher), NULL, NULL, NULL, Bool_val(forenc)) == 0) {
        EVP_CIPHER_CTX_reset(ctx);
        EVP_CIPHER_CTX_free(ctx);
        caml_failwith("cannot initialize cipher context");
    }

    // Disable padding: total amount of data encrypted or decrypted must be a
    // multiple of the block size or an error will occur
    EVP_CIPHER_CTX_set_padding(ctx, 0);

    CIPHER_CTX_val(mlctx) = ctx;
    CAMLreturn(mlctx);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_fini(value mlctx) {
    EVP_CIPHER_CTX *ctx = NULL;

    CAMLparam1(mlctx);

    if ((ctx = CIPHER_CTX_val(mlctx)) != NULL) {
        EVP_CIPHER_CTX_reset(ctx);
        EVP_CIPHER_CTX_free(ctx);
        CIPHER_CTX_val(mlctx) = NULL;
    }

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_block_size(value mlctx) {
    EVP_CIPHER_CTX *ctx = NULL;

    CAMLparam1(mlctx);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL)
      caml_failwith("CIPHER_CTX has been disposed");

    CAMLreturn(Val_int(EVP_CIPHER_CTX_block_size(ctx)));
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_key_length(value mlctx) {
    EVP_CIPHER_CTX *ctx = NULL;

    CAMLparam1(mlctx);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL)
        caml_failwith("CIPHER_CTX has been disposed");

    CAMLreturn(Val_int(EVP_CIPHER_CTX_key_length(ctx)));
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_iv_length(value mlctx) {
    EVP_CIPHER_CTX *ctx = NULL;

    CAMLparam1(mlctx);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL)
        caml_failwith("CIPHER_CTX has been disposed");

    CAMLreturn(Val_int(EVP_CIPHER_CTX_iv_length(ctx)));
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_set_key(value mlctx, value key) {
    EVP_CIPHER_CTX *ctx = NULL;

    CAMLparam2(mlctx, key);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL)
        caml_failwith("CIPHER_CTX has been disposed");

    if (EVP_CIPHER_CTX_set_key_length(ctx, caml_string_length(key)) == 0)
        caml_failwith("cannot set CIPHER_CTX key (set_key_length)");

    if (EVP_CipherInit_ex(ctx, NULL, NULL, (uint8_t*) String_val(key), NULL, -1) == 0)
        caml_failwith("cannot set CIPHER_CTX_key");

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_set_iv(value mlctx, value iv, value variable_iv_length) {
    EVP_CIPHER_CTX *ctx = NULL;

    CAMLparam3(mlctx, iv, variable_iv_length);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL)
        caml_failwith("CIPHER_CTX has been disposed");

    ERR_clear_error();

    if(Bool_val(variable_iv_length) && EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, caml_string_length(iv), NULL) != 1) {
        unsigned long err = ERR_peek_last_error();
        char* err_string = ERR_error_string(err, NULL);
        caml_failwith(err_string);
    }

    if (EVP_CipherInit_ex(ctx, NULL, NULL, NULL, (uint8_t*) String_val(iv), -1) == 0)
        caml_failwith("cannot set CIPHER_CTX_iv");

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_set_tag(value mlctx, value tag) {
    EVP_CIPHER_CTX *ctx = NULL;
    int olen = 0;
    int tlen = 0;

    CAMLparam2(mlctx, tag);
    CAMLlocal1(output);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL)
        caml_failwith("CIPHER_CTX has been disposed");

    // Hardcoded tag length for AES-{128,256}-GCM, may need to be revised to
    // support other ciphers
    tlen = 16;

    if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_TAG, tlen, String_val(tag)) != 1)
       caml_failwith("failed to set AEAD tag");

    olen   = EVP_MAX_BLOCK_LENGTH;
    output = caml_alloc_string(olen);

    if ((EVP_DecryptFinal_ex(ctx, (uint8_t*) output, &olen) != 1) || (olen != 0))
	  CAMLreturn(Val_false);
//        caml_failwith("ciphertext and/or additional data authentication failed");

    CAMLreturn(Val_true);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_get_tag(value mlctx) {
    EVP_CIPHER_CTX *ctx = NULL;
    int olen = 0;
    int tlen = 0;

    CAMLparam1(mlctx);
    CAMLlocal2(output, tag);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL)
        caml_failwith("CIPHER_CTX has been disposed");

    olen   = EVP_MAX_BLOCK_LENGTH;
    output = caml_alloc_string(olen);

    if ((EVP_EncryptFinal_ex(ctx, (uint8_t*) output, &olen) != 1) || (olen != 0))
        caml_failwith("final encryption failed");

    // Hardcoded tag length for AES-{128,256}-GCM, may need to be revised to
    // support other ciphers
    tlen = 16;
    tag  = caml_alloc_string(tlen);

    if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_GET_TAG, tlen, (uint8_t*) tag) != 1)
       caml_failwith("failed to get AEAD tag");

    CAMLreturn(tag);
}

/* ------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_process(value mlctx, value data) {
    EVP_CIPHER_CTX *ctx = NULL;
    int olen = 0;

    CAMLparam2(mlctx, data);
    CAMLlocal1(output);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL)
        caml_failwith("CIPHER_CTX has been disposed");

    if (caml_string_length(data) % EVP_CIPHER_CTX_block_size(ctx) != 0)
        caml_failwith("partial block encryption/decryption not supported");

    olen   = caml_string_length(data);
    output = caml_alloc_string(olen);

    if (EVP_CipherUpdate(ctx, (uint8_t*) output, &olen, (uint8_t*) String_val(data), olen) == 0)
        caml_failwith("encryption/decryption failed");

    if ((size_t) olen != caml_string_length(data))
        caml_failwith("EVP_CIPHER_CTX_process(): internal error");

    CAMLreturn(output);
}

CAMLprim value ocaml_EVP_CIPHER_CTX_set_additional_data(value mlctx, value data) {
    EVP_CIPHER_CTX *ctx = NULL;
    int olen = 0;

    CAMLparam2(mlctx, data);
    CAMLlocal1(output);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL)
        caml_failwith("CIPHER_CTX has been disposed");

    olen   = caml_string_length(data);
    output = caml_alloc_string(olen);

    if (EVP_CipherUpdate(ctx, NULL, &olen, (uint8_t*) String_val(data), olen) == 0)
        caml_failwith("failed to set additional data");

    if ((size_t) olen != caml_string_length(data))
        caml_failwith("EVP_CIPHER_CTX_process(): internal error");

    CAMLreturn(output);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_HMAC(value md, value key, value data) {
    int klen = 0;
    unsigned int olen = 0;

    CAMLparam3(md, key,  data);
    CAMLlocal1(output);

    klen = caml_string_length(key);

    olen   = EVP_MD_size(MD_val(md));
    output = caml_alloc_string(olen);

    if (HMAC(MD_val(md),
             (uint8_t*) String_val(key   ), klen,
             (uint8_t*) String_val(data  ), caml_string_length(data),
             (uint8_t*) String_val(output), &olen) == NULL)
      caml_failwith("EVP_HMAC failed");

    if (olen != (unsigned) EVP_MD_size(MD_val(md)))
      caml_failwith("ocaml_EVP_HMAC(): internal error");

    CAMLreturn(output);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_rand_bytes(value length) {
    CAMLparam1(length);
    CAMLlocal1(output);

    output = caml_alloc_string(Int_val(length));

    if (RAND_bytes((uint8_t*) String_val(output), Int_val(length)) == 0)
      caml_failwith("RAND_bytes failed");

    CAMLreturn(output);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_rand_status(value unit) {
    CAMLparam1(unit);
    CAMLreturn(RAND_status() ? Val_true : Val_false);
}

/* -------------------------------------------------------------------- */
#define RSA_val(v) (*((RSA**) Data_custom_val(v)))

#define PD_NONE  0
#define PD_PKCS1 1

static void ocaml_rsa_finalize(value mlctx) {
    RSA *rsa = RSA_val(mlctx);

    if (rsa != NULL)
        RSA_free(rsa);
}

static struct custom_operations evp_rsa_ops = {
  .identifier  = "ocaml_rsa_ctx",
  .finalize    = ocaml_rsa_finalize,
  .compare     = custom_compare_default,
  .hash        = custom_hash_default,
  .serialize   = custom_serialize_default,
  .deserialize = custom_deserialize_default,
};

/* -------------------------------------------------------------------- */
static int RSAPadding_val(value mlvalue) {
    switch (Int_val(mlvalue)) {
    case PD_NONE : return RSA_NO_PADDING;
    case PD_PKCS1: return RSA_PKCS1_PADDING;
    }

    abort();
}

/* -------------------------------------------------------------------- */
#define RSAKey_mod(v)     (Field(v, 0))
#define RSAKey_pub_exp(v) (Field(v, 1))
#define RSAKey_pvr_exp(v) (Field(v, 2))

#define RSAKey_set_mod(v, x)     Store_field(v, 0, x)
#define RSAKey_set_pub_exp(v, x) Store_field(v, 1, x)
#define RSAKey_set_prv_exp(v, x) Store_field(v, 2, x)

#define RSAKeyAlloc() (caml_alloc_tuple(3))

/* -------------------------------------------------------------------- */
static const EVP_MD *RSADigest_val(value digest) {
    switch (Int_val(digest)) {
      case 0: return EVP_md5();
      case 1: return EVP_sha1();
      case 2: return EVP_sha224();
      case 3: return EVP_sha256();
      case 4: return EVP_sha384();
      case 5: return EVP_sha512();
    }
    abort();
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_rsa_new(value unit) {
    RSA *rsa = NULL;

    CAMLparam1(unit);
    CAMLlocal1(mlrsa);

    mlrsa = caml_alloc_custom(&evp_rsa_ops, sizeof(RSA*), 0, 1);

    if ((rsa = RSA_new()) == NULL)
      caml_failwith("cannot allocate RSA structure");

    (void) RSA_set_method(rsa, RSA_PKCS1_OpenSSL());

    RSA_val(mlrsa) = rsa;
    CAMLreturn(mlrsa);
}

/* -------------------------------------------------------------------- */

CAMLprim value ocaml_rsa_fini(value mlrsa) {
    CAMLparam1(mlrsa);

    if (RSA_val(mlrsa) != NULL) {
        RSA_free(RSA_val(mlrsa));
        RSA_val(mlrsa) = NULL;
    }

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_rsa_gen_key(value mlsz, value mlexp) {
    RSA *rsa = RSA_new();
    BIGNUM *bn_mlexp = BN_new();

    CAMLparam2(mlsz, mlexp);

    if (rsa == NULL || bn_mlexp == NULL)
      caml_failwith("RSA:genkey failed");

#   ifdef DEBUG
      printf("ocaml_rsa_gen_key: modulus size will be of %d bits (%d bytes)\n", Int_val(mlsz), Int_val(mlsz)/8);
#   endif

    BN_set_word(bn_mlexp, Int_val(mlexp));
    if (RSA_generate_key_ex(rsa, Int_val(mlsz), bn_mlexp, NULL) != 1) {
      RSA_free(rsa);
      BN_free(bn_mlexp);
      caml_failwith("RSA:genkey failed");
    }

    CAMLlocal3(e, n, d);
    const BIGNUM *b_n, *b_e, *b_d;
    RSA_get0_key(rsa, &b_n, &b_e, &b_d);

    n = caml_alloc_string(BN_num_bytes(b_n));
    e = caml_alloc_string(BN_num_bytes(b_e));
    d = caml_alloc_string(BN_num_bytes(b_d));

    (void) BN_bn2bin(b_n, (uint8_t*) String_val(n));
    (void) BN_bn2bin(b_e, (uint8_t*) String_val(e));
    (void) BN_bn2bin(b_d, (uint8_t*) String_val(d));

    BN_free(bn_mlexp);
    RSA_free(rsa);

#   ifdef DEBUG
      printf("ocaml_rsa_gen_key: length(n)=%zu, length(e)=%zu, length(d)=%zu\n",
          caml_string_length(n), caml_string_length(e), caml_string_length(d));
#   endif

    CAMLlocal1(ret);
    ret = caml_alloc_tuple(3);
    Field(ret, 0) = n;
    Field(ret, 1) = e;
    Field(ret, 2) = d;
    CAMLreturn(ret);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_rsa_set_key(value mlrsa, value mlkey) {
    RSA *rsa = NULL;
    BIGNUM *mod = NULL;
    BIGNUM *pub = NULL;
    BIGNUM *prv = NULL;

    CAMLparam2(mlrsa, mlkey);
    CAMLlocal3(mlmod, mlpub, mlprv);

    const char* failure = "";

    if ((rsa = RSA_val(mlrsa)) == NULL)
      caml_failwith("RSA has been disposed");


    mlmod = RSAKey_mod(mlkey);
    mlpub = RSAKey_pub_exp(mlkey);
    mlprv = RSAKey_pvr_exp(mlkey);

    size_t modbuf_length, pubbuf_length;
    uint8_t* modbuf = buffer_of_platform_bytes(mlmod, &modbuf_length);
    uint8_t* pubbuf = buffer_of_platform_bytes(mlpub, &pubbuf_length);
    uint8_t* prvbuf = NULL;

    if (modbuf == NULL || pubbuf == NULL || !modbuf_length || !pubbuf_length) {
      failure = "ocaml_rsa_set_key: invalid bytes for key parameters";
      goto bailout;
    }

    mod = BN_bin2bn(modbuf, modbuf_length, NULL);
    pub = BN_bin2bn(pubbuf, pubbuf_length, NULL);
#   ifdef DEBUG
      printf("ocaml_rsa_set_key: modbuf_length=%zu, pubbuf_length=%zu\n", modbuf_length, pubbuf_length);
#   endif


    if (Is_block(mlprv)) {
        CAMLlocal1(prvdata);

        prvdata = Field(mlprv, 0);
        size_t prvbuf_length;
        prvbuf = buffer_of_platform_bytes(prvdata, &prvbuf_length);
        if (prvbuf == NULL || !prvbuf_length) {
          failure = "ocaml_rsa_set_key: invalid bytes for private key";
          goto bailout;
        }

        prv = BN_bin2bn(prvbuf, prvbuf_length, NULL);
#       ifdef DEBUG
          printf("ocaml_rsa_set_key: prvbuf_length=%zu\n", prvbuf_length);
#       endif
    }

    if (mod == NULL || pub == NULL || (prv == NULL && Is_block(mlprv))) {
      failure = "ocaml_rsa_set_key: cannot allocate internal structure for keys";
      goto bailout;
    }

    RSA_set0_key(rsa, mod, pub, prv);
    free(modbuf);
    free(pubbuf);
    if (prvbuf != NULL)
      free(prvbuf);

    CAMLreturn(Val_unit);

bailout:
    if (mod != NULL) BN_clear_free(mod);
    if (pub != NULL) BN_clear_free(pub);
    if (prv != NULL) BN_clear_free(prv);
    if (modbuf != NULL) free(modbuf);
    if (pubbuf != NULL) free(pubbuf);
    if (prvbuf != NULL) free(prvbuf);
    caml_failwith(failure);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_rsa_get_key(value mlrsa) {
  RSA *rsa = NULL;

  CAMLparam1(mlrsa);

  if ((rsa = RSA_val(mlrsa)) == NULL)
    caml_failwith("RSA has been disposed");

  CAMLlocal3(n, e, d);
  const BIGNUM *b_n, *b_e, *b_d;
  RSA_get0_key(rsa, &b_n, &b_e, &b_d);

  n = caml_alloc_string(BN_num_bytes(b_n));
  e = caml_alloc_string(BN_num_bytes(b_e));

  (void) BN_bn2bin(b_n, (uint8_t*) String_val(n));
  (void) BN_bn2bin(b_e, (uint8_t*) String_val(e));

  CAMLlocal1(ret);
  ret = caml_alloc_tuple(3);

  Field(ret, 0) = n;
  Field(ret, 1) = e;

  if (b_d == NULL)
    Field(ret, 2) = Val_none;
  else {
    d = caml_alloc_string(BN_num_bytes(b_d));
    (void) BN_bn2bin(b_d, (uint8_t*) String_val(d));
    Field(ret, 2) = Val_some(d);
  }

  CAMLreturn(ret);
}

/* -------------------------------------------------------------------- */
typedef int (rsa_dec_t)(int, const uint8_t *, uint8_t *, RSA *, int);
typedef int (rsa_enc_t)(int, const uint8_t *, uint8_t *, RSA *, int);

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_rsa_encrypt(value mlrsa, value mlprv, value mlpadding, value data) {
    RSA    *rsa = NULL;
    size_t rsasz = 0, pdsz = 0;
    int    padding = -1;

    rsa_enc_t *enc = NULL;

    CAMLparam4(mlrsa, mlprv, mlpadding, data);
    CAMLlocal1(output);

    if ((rsa = RSA_val(mlrsa)) == NULL)
        caml_failwith("RSA has been disposed");

    const BIGNUM *b_n, *b_e, *b_d;
    RSA_get0_key(rsa, &b_n, &b_e, &b_d);
    if (b_e == NULL || (Bool_val(mlprv) && b_d == NULL))
        caml_failwith("RSA:encrypt: missing key");

    padding = RSAPadding_val(mlpadding);
    rsasz   = RSA_size(rsa);

    switch (padding) {
    case RSA_NO_PADDING   : pdsz =  0; break ;
    case RSA_PKCS1_PADDING: pdsz = 11; break ;

    default:
        abort();
    }

#   ifdef DEBUG
        printf("caml_string_length(data)=%zu, RSA_size(rsa)=%u\n", caml_string_length(data), RSA_size(rsa));
#   endif
    if (caml_string_length(data) > (rsasz - pdsz))
        caml_failwith("RSA:encrypt: invalid data length");

    output = caml_alloc_string(rsasz);

    enc = Bool_val(mlprv) ? &RSA_private_encrypt : &RSA_public_encrypt;

    ERR_clear_error();

    if (enc(caml_string_length(data),
            (uint8_t*) String_val(data),
            (uint8_t*) String_val(output),
            rsa, padding) < 0) {
      unsigned long err = ERR_peek_last_error();
      char* err_string = ERR_error_string(err, NULL);
      caml_failwith(err_string);
    }

    CAMLreturn(output);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_rsa_decrypt(value mlrsa, value mlprv, value mlpadding, value data) {
    RSA    *rsa = NULL;
    size_t  rsasz = 0;
    int     padding = -1;
    ssize_t rr;

    rsa_dec_t *dec = NULL;

    CAMLparam4(mlrsa, mlprv, mlpadding, data);
    CAMLlocal2(buffer, output);

    if ((rsa = RSA_val(mlrsa)) == NULL)
        caml_failwith("RSA has been disposed");

    const BIGNUM *b_n, *b_e, *b_d;
    RSA_get0_key(rsa, &b_n, &b_e, &b_d);

    if (b_e == NULL || (Bool_val(mlprv) && b_d == NULL))
        caml_failwith("RSA:decrypt: missing key");

    padding = RSAPadding_val(mlpadding);
    rsasz   = RSA_size(rsa);

    if (caml_string_length(data) != rsasz)
        caml_failwith("RSA:decrypt: invalid data length");

    buffer = caml_alloc_string(rsasz);

    dec = Bool_val(mlprv) ? RSA_private_decrypt : RSA_public_decrypt;

    ERR_clear_error();

    if ((rr = dec(rsasz,
                  (uint8_t*) String_val(data),
                  (uint8_t*) String_val(buffer),
                  rsa, padding)) < 0) {
      unsigned long err = ERR_peek_last_error();
      char* err_string = ERR_error_string(err, NULL);
      caml_failwith(err_string);
    }

    output = caml_alloc_string(rr);
    memcpy(String_val(output), String_val(buffer), rr);

    CAMLreturn(output);
}

/* -------------------------------------------------------------------- */
// ADL(Aug. 3) Rewrote these functions to use the EVP_DigestSign and EVP_DigestVerify
// in order to support PSS signatures as well as PKCS#1
CAMLprim value ocaml_rsa_sign(value mlrsa, value pss, value mldigest, value data) {
    CAMLparam4(mlrsa, pss, mldigest, data);
    CAMLlocal1(output);

    RSA *rsa = NULL;
    if ((rsa = RSA_val(mlrsa)) == NULL) caml_failwith("RSA has been disposed");
    size_t olen = RSA_size(rsa);
    output = caml_alloc_string(olen);

    if(mldigest == Val_none) { // MD5+SHA1
      if(pss == Val_true) caml_failwith("ocaml_rsa_sign: can't use PSS with MD5SHA1");
      if (RSA_sign(NID_md5_sha1, (uint8_t*) String_val(data), caml_string_length(data),
                 (uint8_t*) String_val(output), (unsigned*) &olen, rsa) != 1) {
        unsigned long err = ERR_peek_last_error();
        char* err_string = ERR_error_string(err, NULL);
        caml_failwith(err_string);
      }
    } else { // Single hash signature
      EVP_MD_CTX* md_ctx = EVP_MD_CTX_new();
      const EVP_MD *md = RSADigest_val(Some_val(mldigest));
      EVP_PKEY* pkey = EVP_PKEY_new();
      EVP_PKEY_CTX* key_ctx = NULL;

      if(!EVP_PKEY_set1_RSA(pkey, rsa))
        caml_failwith("openssl_stub: EVP_PKEY_set1_RSA");
      if(EVP_DigestSignInit(md_ctx, &key_ctx, md, NULL, pkey) != 1)
        caml_failwith("openssl_stub: EVP_DigestSignInit");

      if(pss == Val_true) {
        if (EVP_PKEY_CTX_set_rsa_padding(key_ctx, RSA_PKCS1_PSS_PADDING) != 1)
          caml_failwith("openssl_stub: EVP_PKEY_CTX_set_rsa_padding PSS");
        if(EVP_PKEY_CTX_set_rsa_pss_saltlen(key_ctx, RSA_PSS_SALTLEN_DIGEST) != 1)
          caml_failwith("openssl_stub: EVP_PKEY_CTX_set_rsa_pss_saltlen");
      } else {
        if (EVP_PKEY_CTX_set_rsa_padding(key_ctx, RSA_PKCS1_PADDING) != 1)
          caml_failwith("openssl_stub: EVP_PKEY_CTX_set_rsa_padding PKCS1");
      }

      if(EVP_DigestSign(md_ctx, (uint8_t*)String_val(output), &olen,
          (uint8_t*) String_val(data), caml_string_length(data)) != 1) {
  #ifdef DEBUG
        printf("ocaml_rsa_sign: caml_string_length(data)=%zu, RSA_size(rsa)=%u\n",
          caml_string_length(data), RSA_size(rsa));
  #endif
        unsigned long err = ERR_peek_last_error();
        char* err_string = ERR_error_string(err, NULL);
        caml_failwith(err_string);
      }

      EVP_MD_CTX_free(md_ctx);
      EVP_PKEY_free(pkey);
    }

    if (olen != caml_string_length(output))
    {
      CAMLlocal1(sig);
      sig = caml_alloc_string(olen);
      memcpy(String_val(sig), String_val(output), olen);
      CAMLreturn(sig);
    }

    CAMLreturn(output);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_rsa_verify(value mlrsa, value pss, value mldigest, value data, value sig) {
  CAMLparam5(mlrsa, pss, mldigest, data, sig);
  RSA *rsa = NULL; int rr = -1;
  if ((rsa = RSA_val(mlrsa)) == NULL) caml_failwith("RSA has been disposed");

  if(mldigest == Val_none) {
    if(pss == Val_true) caml_failwith("ocaml_rsa_verify: can't use PSS with MD5SHA1");
    rr = RSA_verify(NID_md5_sha1, (uint8_t*) String_val(data), caml_string_length(data),
                    (uint8_t*) String_val(sig), caml_string_length(sig), rsa);
  } else {
    EVP_MD_CTX* md_ctx = EVP_MD_CTX_new();
    const EVP_MD *md = RSADigest_val(Some_val(mldigest));
    EVP_PKEY* pkey = EVP_PKEY_new();
    EVP_PKEY_CTX* key_ctx = NULL;

    if(!EVP_PKEY_set1_RSA(pkey, rsa))
      caml_failwith("openssl_stub: EVP_PKEY_set1_RSA");
    if(EVP_DigestVerifyInit(md_ctx, &key_ctx, md, NULL, pkey) != 1)
      caml_failwith("openssl_stub: EVP_DigestVerifyInit");

    if(pss == Val_true) {
      if (EVP_PKEY_CTX_set_rsa_padding(key_ctx, RSA_PKCS1_PSS_PADDING) != 1)
        caml_failwith("openssl_stub: EVP_PKEY_CTX_set_rsa_padding PSS");
      if(EVP_PKEY_CTX_set_rsa_pss_saltlen(key_ctx, RSA_PSS_SALTLEN_DIGEST) != 1)
        caml_failwith("openssl_stub: EVP_PKEY_CTX_set_rsa_pss_saltlen");
    } else {
      if (EVP_PKEY_CTX_set_rsa_padding(key_ctx, RSA_PKCS1_PADDING) != 1)
        caml_failwith("openssl_stub: EVP_PKEY_CTX_set_rsa_padding PKCS1");
    }

    rr = EVP_DigestVerify(md_ctx,
         (const unsigned char*) String_val(sig), caml_string_length(sig),
         (const unsigned char*) String_val(data), caml_string_length(data));

    EVP_MD_CTX_free(md_ctx);
    EVP_PKEY_free(pkey);
  }

#ifdef DEBUG
  if(rr != 1) {
    unsigned long err = ERR_peek_last_error();
    char* err_string = ERR_error_string(err, NULL);
    printf("ocaml_rsa_verify: %s\n", err_string);
  }
#endif

  CAMLreturn((rr == 1) ? Val_true : Val_false);
}

/* -------------------------------------------------------------------- */
#define DSA_val(v) (*((DSA**) Data_custom_val(v)))

static void ocaml_dsa_finalize(value mlctx) {
    DSA *dsa = DSA_val(mlctx);

    if (dsa != NULL)
        DSA_free(dsa);
}

static struct custom_operations evp_dsa_ops = {
  .identifier  = "ocaml_dsa_ctx",
  .finalize    = ocaml_dsa_finalize,
  .compare     = custom_compare_default,
  .hash        = custom_hash_default,
  .serialize   = custom_serialize_default,
  .deserialize = custom_deserialize_default,
};

/* -------------------------------------------------------------------- */
#define DSAParams_p(v) (Field(v, 0))
#define DSAParams_q(v) (Field(v, 1))
#define DSAParams_g(v) (Field(v, 2))

#define DSAParams_set_p(v, x) Store_field(v, 0, x)
#define DSAParams_set_q(v, x) Store_field(v, 1, x)
#define DSAParams_set_g(v, x) Store_field(v, 2, x)

#define DSAParamsAlloc() (caml_alloc_tuple(3))

/* -------------------------------------------------------------------- */
#define DSAKey_params(v) (Field(v, 0))
#define DSAKey_pub(v)    (Field(v, 1))
#define DSAKey_prv(v)    (Field(v, 2))

#define DSAKey_set_params(v, x) Store_field(v, 0, x)
#define DSAKey_set_pub(v, x)    Store_field(v, 1, x)
#define DSAKey_set_prv(v, x)    Store_field(v, 2, x)

#define DSAKeyAlloc() (caml_alloc_tuple(3))

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dsa_new(value unit) {
    DSA *dsa = NULL;

    CAMLparam1(unit);
    CAMLlocal1(mldsa);

    mldsa = caml_alloc_custom(&evp_dsa_ops, sizeof(DSA*), 0, 1);

    if ((dsa = DSA_new()) == NULL)
        caml_failwith("cannot allocated DSA structure");

    DSA_val(mldsa) = dsa;
    CAMLreturn(mldsa);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dsa_fini(value mldsa) {
    CAMLparam1(mldsa);

    if (DSA_val(mldsa) != NULL) {
        DSA_free(DSA_val(mldsa));
        DSA_val(mldsa) = NULL;
    }

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dsa_gen_params(value size) {
    DSA* dsa = DSA_new();

    CAMLparam1(size);
    CAMLlocal3(p, q, g);

    if (DSA_generate_parameters_ex(dsa, Int_val(size), NULL, 0, NULL, NULL, NULL) != 1)
        caml_failwith("DSA:genparams failed");

    const BIGNUM *b_p, *b_q, *b_g;
    DSA_get0_pqg(dsa, &b_p, &b_q, &b_g);
    p = caml_alloc_string(BN_num_bytes(b_p));
    q = caml_alloc_string(BN_num_bytes(b_q));
    g = caml_alloc_string(BN_num_bytes(b_g));

    (void) BN_bn2bin(b_p, (uint8_t*) String_val(p));
    (void) BN_bn2bin(b_q, (uint8_t*) String_val(q));
    (void) BN_bn2bin(b_g, (uint8_t*) String_val(g));

    CAMLlocal1(ret);
    ret = caml_alloc_tuple(3);
    Field(ret, 0) = p;
    Field(ret, 1) = q;
    Field(ret, 2) = g;

    DSA_free(dsa);

    CAMLreturn(ret);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dsa_gen_key(value mlparams) {
    DSA *dsa = NULL;

    CAMLparam1(mlparams);
    CAMLlocal3(mlp, mlq, mlg);
    CAMLlocal2(mlpub, mlprv);

    const char* failure = "";

    if ((dsa = DSA_new()) == NULL)
        caml_failwith("DSA:genkey: failed to create a DSA structure");

    mlp = DSAParams_p(mlparams);
    mlq = DSAParams_q(mlparams);
    mlg = DSAParams_g(mlparams);

    size_t mlp_len = 0, mlq_len = 0, mlg_len = 0;
    uint8_t* mlp_buf = buffer_of_platform_bytes(mlp, &mlp_len);
    uint8_t* mlq_buf = buffer_of_platform_bytes(mlq, &mlq_len);
    uint8_t* mlg_buf = buffer_of_platform_bytes(mlg, &mlg_len);
    if (mlp_buf == NULL || mlq_buf == NULL || mlg_buf == NULL) {
      failure = "ocaml_dsa_gen_key: invalid Platform.Bytes.bytes";
      goto bailout;
    }

    BIGNUM *b_p = BN_bin2bn(mlp_buf, mlp_len, NULL);
    BIGNUM *b_q = BN_bin2bn(mlq_buf, mlq_len, NULL);
    BIGNUM *b_g = BN_bin2bn(mlg_buf, mlg_len, NULL);
    DSA_set0_pqg(dsa, b_p, b_q, b_g);

    if (DSA_generate_key(dsa) == 0) {
      failure = "DSA:genkey: DSA_generate_key failed";
      goto bailout;
    }

    const BIGNUM *b_pub, *b_priv;
    DSA_get0_key(dsa, &b_pub, &b_priv);
    mlpub = caml_alloc_string(BN_num_bytes(b_pub));
    mlprv = caml_alloc_string(BN_num_bytes(b_priv));

    (void) BN_bn2bin(b_pub , (uint8_t*) String_val(mlpub));
    (void) BN_bn2bin(b_priv, (uint8_t*) String_val(mlprv));

    CAMLlocal1(ret);
    ret = caml_alloc_tuple(2);
    Field(ret, 0) = mlpub;
    Field(ret, 1) = mlprv;

    free(mlp_buf);
    free(mlq_buf);
    free(mlg_buf);

    CAMLreturn(ret);

bailout:
    if (mlp_buf != NULL) free(mlp_buf);
    if (mlq_buf != NULL) free(mlq_buf);
    if (mlg_buf != NULL) free(mlg_buf);
    // Free the [dsa] structure _and its components_ (the BIGNUM's).
    DSA_free(dsa);

    caml_failwith(failure);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dsa_get_key(value mldsa) {
  DSA *dsa = NULL;

  CAMLparam1(mldsa);

  if ((dsa = DSA_val(mldsa)) == NULL)
    caml_failwith("DSA has been disposed");

  CAMLlocal5(p, g, q, pk, sk);
  const BIGNUM *b_p, *b_q, *b_g;
  DSA_get0_pqg(dsa, &b_p, &b_q, &b_g);

  p = caml_alloc_string(BN_num_bytes(b_p));
  q = caml_alloc_string(BN_num_bytes(b_q));
  g = caml_alloc_string(BN_num_bytes(b_g));

  const BIGNUM *b_pub, *b_priv;
  DSA_get0_key(dsa, &b_pub, &b_priv);
  pk = caml_alloc_string(BN_num_bytes(b_pub));

  (void) BN_bn2bin(b_p, (uint8_t*) String_val(p));
  (void) BN_bn2bin(b_q, (uint8_t*) String_val(q));
  (void) BN_bn2bin(b_g, (uint8_t*) String_val(g));
  (void) BN_bn2bin(b_pub, (uint8_t*) String_val(pk));

  CAMLlocal1(ret);
  ret = caml_alloc_tuple(5);

  Field(ret, 0) = p;
  Field(ret, 1) = q;
  Field(ret, 2) = g;
  Field(ret, 3) = pk;

  if (b_priv == NULL)
    Field(ret, 4) = Val_none;
  else {
    sk = caml_alloc_string(BN_num_bytes(b_priv));
    (void) BN_bn2bin(b_priv, (uint8_t*) String_val(sk));
    Field(ret, 4) = Val_some(sk);
  }

  CAMLreturn(ret);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dsa_set_key(value mldsa, value mlkey) {
    DSA *dsa = NULL;
    BIGNUM *p = NULL;
    BIGNUM *q = NULL;
    BIGNUM *g = NULL;
    BIGNUM *pub = NULL;
    BIGNUM *prv = NULL;

    CAMLparam2(mldsa, mlkey);
    CAMLlocal5(mlp, mlq, mlg, mlpub, mlprv);

    const char* failure = "";

    if ((dsa = DSA_val(mldsa)) == NULL)
        caml_failwith("DSA has been disposed");

    const BIGNUM *b_p, *b_q, *b_g, *b_pub, *b_priv;
    DSA_get0_pqg(dsa, &b_p, &b_q, &b_g);
    DSA_get0_key(dsa, &b_pub, &b_priv);

    mlp = DSAParams_p(DSAKey_params(mlkey));
    mlq = DSAParams_q(DSAKey_params(mlkey));
    mlg = DSAParams_g(DSAKey_params(mlkey));
    mlpub = DSAKey_pub(mlkey);
    mlprv = DSAKey_prv(mlkey);

    size_t mlp_len = 0, mlq_len = 0, mlg_len = 0, mlpub_len = 0, mlprv_len = 0;
    uint8_t* mlp_buf = buffer_of_platform_bytes(mlp, &mlp_len);
    uint8_t* mlq_buf = buffer_of_platform_bytes(mlq, &mlq_len);
    uint8_t* mlg_buf = buffer_of_platform_bytes(mlg, &mlg_len);
    uint8_t* mlpub_buf = buffer_of_platform_bytes(mlpub, &mlpub_len);
    uint8_t* mlprv_buf = NULL;
    if (mlp_buf == NULL || mlq_buf == NULL || mlg_buf == NULL || mlpub_buf == NULL) {
      failure = "ocaml_dsa_set_key: invalid Platform.Bytes.byte";
      goto bailout;
    }

    p = BN_bin2bn(mlp_buf, mlp_len, NULL);
    q = BN_bin2bn(mlq_buf, mlq_len, NULL);
    g = BN_bin2bn(mlg_buf, mlg_len, NULL);
    pub = BN_bin2bn(mlpub_buf, mlpub_len, NULL);

    if (Is_block(mlprv)) {
#       ifdef DEBUG
          printf("ocaml_dsa_set_key: got a private key\n");
#       endif
        CAMLlocal1(prvdata);

        prvdata = Field(mlprv, 0);
        mlprv_buf = buffer_of_platform_bytes(prvdata, &mlprv_len);
        if (mlprv_buf == NULL) {
          failure = "ocaml_dsa_set_key: invalid Platform.Bytes.byte";
          goto bailout;
        }
        prv = BN_bin2bn(mlprv_buf, mlprv_len, NULL);
    }

    if (p == NULL || q == NULL || g == NULL) {
        failure = "ocaml_dsa_set_key: cannot allocate internal structure for parameters";
        goto bailout;
    }

    if (pub == NULL || (Is_block(mlprv) && prv == NULL)) {
        failure = "ocaml_dsa_set_key: cannot allocate internal structure for keys";
        goto bailout;
    }

    DSA_set0_pqg(dsa, p, q, g);
    DSA_set0_key(dsa, pub, prv);

    free(mlp_buf);
    free(mlq_buf);
    free(mlg_buf);
    free(mlpub_buf);
    if (mlprv_buf != NULL)
      free(mlprv_buf);

    CAMLreturn(Val_unit);

 bailout:
    if (p   != NULL) BN_clear_free(p);
    if (q   != NULL) BN_clear_free(q);
    if (g   != NULL) BN_clear_free(g);
    if (pub != NULL) BN_clear_free(pub);
    if (prv != NULL) BN_clear_free(prv);
    if (mlp_buf != NULL) free(mlp_buf);
    if (mlq_buf != NULL) free(mlq_buf);
    if (mlg_buf != NULL) free(mlg_buf);
    if (mlpub_buf != NULL) free(mlpub_buf);
    if (mlprv_buf != NULL) free(mlprv_buf);
    DSA_free(dsa);

    caml_failwith(failure);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dsa_sign(value mldsa, value data) {
    DSA *dsa = NULL;
    size_t olen = 0;

    CAMLparam2(mldsa, data);
    CAMLlocal1(output);

    if ((dsa = DSA_val(mldsa)) == NULL)
        caml_failwith("DSA has been disposed");

    const BIGNUM *b_p, *b_q, *b_g, *b_pub, *b_priv;
    DSA_get0_pqg(dsa, &b_p, &b_q, &b_g);
    DSA_get0_key(dsa, &b_pub, &b_priv);

    if (b_pub == NULL || b_priv == NULL)
        caml_failwith("DSA keys not set");

    output = caml_alloc_string(DSA_size(dsa));
    olen = caml_string_length(output);

    ERR_clear_error();

    if (DSA_sign(0,             /* ignored */
                 (uint8_t*) String_val(data),
                 caml_string_length(data),
                 (uint8_t*) String_val(output),
                 (unsigned*) &olen, dsa) == 0) {
      unsigned long err = ERR_peek_last_error();
      char* err_string = ERR_error_string(err, NULL);
      caml_failwith(err_string);
    }

    if (olen != caml_string_length(output)) {
        CAMLlocal1(sig);

        sig = caml_alloc_string(olen);
        memcpy(String_val(sig), String_val(output), olen);
        CAMLreturn(sig);
    }

    CAMLreturn(output);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dsa_verify(value mldsa, value data, value sig) {
    DSA *dsa = NULL;
    int rr = -1;

    CAMLparam3(mldsa, data, sig);

    if ((dsa = DSA_val(mldsa)) == NULL)
        caml_failwith("DSA has been disposed");

    const BIGNUM *b_p, *b_q, *b_g, *b_pub, *b_priv;
    DSA_get0_pqg(dsa, &b_p, &b_q, &b_g);
    DSA_get0_key(dsa, &b_pub, &b_priv);

    if (b_pub == NULL)
        caml_failwith("DSA:verify: DSA (public) keys not set");

    ERR_clear_error();

    rr = DSA_verify(0, /* ignored */
                    (uint8_t*) String_val(data),
                    caml_string_length(data),
                    (uint8_t*) String_val(sig),
                    caml_string_length(sig),
                    dsa);

    if (rr == -1) {
      unsigned long err = ERR_peek_last_error();
      char* err_string = ERR_error_string(err, NULL);
      caml_failwith(err_string);
    }

    CAMLreturn((rr > 0) ? Val_true : Val_false);
}


/* -------------------------------------------------------------------- */
#define DH_val(v) (*((DH**) Data_custom_val(v)))

static void ocaml_dh_finalize(value mlctx) {
    DH *dh = DH_val(mlctx);

    if (dh != NULL)
        DH_free(dh);
}

static struct custom_operations evp_dh_ops = {
  .identifier  = "ocaml_dh_ctx",
  .finalize    = ocaml_dh_finalize,
  .compare     = custom_compare_default,
  .hash        = custom_hash_default,
  .serialize   = custom_serialize_default,
  .deserialize = custom_deserialize_default,
};

/* -------------------------------------------------------------------- */
#define DHParams_p(v) (Field(v, 0))
#define DHParams_g(v) (Field(v, 1))

#define DHParams_set_p(v, x) Store_field(v, 0, x)
#define DHParams_set_g(v, x) Store_field(v, 1, x)
#define DHParams_set_q(v, x) Store_field(v, 2, x)
#define DHParams_set_safe(v, x) Store_field(v, 3, x)

#define DHParamsAlloc() (caml_alloc_tuple(2))

/* -------------------------------------------------------------------- */
#define DHKey_params(v) (Field(v, 0))
#define DHKey_pub(v)    (Field(v, 1))
#define DHKey_prv(v)    (Field(v, 2))

#define DHKey_set_params(v, x) Store_field(v, 0, x)
#define DHKey_set_pub(v, x)    Store_field(v, 1, x)
#define DHKey_set_prv(v, x)    Store_field(v, 2, x)

#define DHKeyAlloc() (caml_alloc_tuple(3))

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dh_new(value unit) {
    DH *dh = NULL;

    CAMLparam1(unit);
    CAMLlocal1(mldh);

    mldh = caml_alloc_custom(&evp_dh_ops, sizeof(DH*), 0, 1);

    if ((dh = DH_new()) == NULL)
      caml_failwith("cannot allocate DH structure");

    DH_val(mldh) = dh;
    CAMLreturn(mldh);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dh_fini(value mldh) {
    CAMLparam1(mldh);

    if (DH_val(mldh) != NULL) {
        DH_free(DH_val(mldh));
        DH_val(mldh) = NULL;
    }

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dh_gen_params(value size, value gen) {
    DH *dh = DH_new();

    CAMLparam1(size);
    CAMLlocal2(p, g);

    if (DH_generate_parameters_ex(dh, Int_val(size), Int_val(gen), NULL) != 1)
        caml_failwith("DH:genparams failed");

    const BIGNUM *b_p, *b_q, *b_g;
    DH_get0_pqg(dh, &b_p, &b_q, &b_g);

    p = caml_alloc_string(BN_num_bytes(b_p));
    g = caml_alloc_string(BN_num_bytes(b_g));

    (void) BN_bn2bin(b_p, (uint8_t*) String_val(p));
    (void) BN_bn2bin(b_g, (uint8_t*) String_val(g));

    CAMLlocal1(ret);
    ret = caml_alloc_tuple(2);
    Field(ret, 0) = p;
    Field(ret, 1) = g;

    DH_free(dh);

    CAMLreturn(ret);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dh_params_of_string(value pem) {
    CAMLparam1(pem);
    CAMLlocal2(mlp, mlg);

    BIO *bio = NULL;
    DH  *dh  = NULL;

    if ((bio = BIO_new_mem_buf(String_val(pem), caml_string_length(pem))) == NULL)
        caml_failwith("DH:params_of_string");

    if ((dh = PEM_read_bio_DHparams(bio, NULL, NULL, NULL)) == NULL)
        caml_failwith("DH:params_of_string");

    const BIGNUM *b_p, *b_q, *b_g;
    DH_get0_pqg(dh, &b_p, &b_q, &b_g);

    mlp = caml_alloc_string(BN_num_bytes(b_p));
    mlg = caml_alloc_string(BN_num_bytes(b_g));

    (void) BN_bn2bin(b_p, (uint8_t*) String_val(mlp));
    (void) BN_bn2bin(b_g, (uint8_t*) String_val(mlg));

    DH_free(dh);
    BIO_free(bio);

    CAMLlocal1(ret);
    ret = caml_alloc_tuple(2);
    Field(ret, 0) = mlp;
    Field(ret, 1) = mlg;
    CAMLreturn(ret);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dh_gen_key(value mlparams) {
    DH *dh = NULL;

    CAMLparam1(mlparams);
    CAMLlocal2(mlp, mlg);
    CAMLlocal2(mlpub, mlprv);

    if ((dh = DH_new()) == NULL)
        caml_failwith("DH:genkey: failed to create a DH structure");

    mlp = DHParams_p(mlparams);
    mlg = DHParams_g(mlparams);

    size_t mlp_len, mlg_len;
    uint8_t* mlp_buf = buffer_of_platform_bytes(mlp, &mlp_len);
    uint8_t* mlg_buf = buffer_of_platform_bytes(mlg, &mlg_len);
    if (mlp_buf == NULL || mlg_buf == NULL) {
      DH_free(dh);
      caml_failwith("ocaml_dh_gen_key: invalid bytes");
    }

    BIGNUM *p = BN_bin2bn(mlp_buf, mlp_len, NULL);
    BIGNUM *g = BN_bin2bn(mlg_buf, mlg_len, NULL);
    DH_set0_pqg(dh, p, NULL, g);

    if (p == NULL || g == NULL) {
        DH_free(dh);
        caml_failwith("DH:genkey: failed dup DH parameters");
    }

    if (DH_generate_key(dh) == 0) {
        DH_free(dh);
        caml_failwith("DH:genkey: DH_generate_key failed");
    }

    const BIGNUM *b_pub, *b_prv;
    DH_get0_key(dh, &b_pub, &b_prv);

    mlpub = caml_alloc_string(BN_num_bytes(b_pub));
    mlprv = caml_alloc_string(BN_num_bytes(b_prv));

    (void) BN_bn2bin(b_pub, (uint8_t*) String_val(mlpub));
    (void) BN_bn2bin(b_prv, (uint8_t*) String_val(mlprv));

    DH_free(dh);
    free(mlp_buf);
    free(mlg_buf);

    CAMLlocal1(ret);
    ret = caml_alloc_tuple(2);
    Field(ret, 0) = mlpub;
    Field(ret, 1) = mlprv;
    CAMLreturn(ret);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dh_set_key(value mldh, value mlkey) {
    CAMLparam2(mldh, mlkey);
    CAMLlocal4(mlp, mlg, mlpub, mlprv);

    DH *dh = NULL;
    BIGNUM *p = NULL;
    BIGNUM *g = NULL;
    BIGNUM *pub = NULL;
    BIGNUM *prv = NULL;
    const char* failure = "";

    if ((dh = DH_val(mldh)) == NULL)
        caml_failwith("DH has been disposed");

    mlp = DHParams_p(DHKey_params(mlkey));
    mlg = DHParams_g(DHKey_params(mlkey));
    mlpub = DHKey_pub(mlkey);
    mlprv = DHKey_prv(mlkey);

    size_t mlp_len, mlg_len, mlpub_len, mlprv_len;
    uint8_t* mlp_buf = buffer_of_platform_bytes(mlp, &mlp_len);
    uint8_t* mlg_buf = buffer_of_platform_bytes(mlg, &mlg_len);
    uint8_t* mlpub_buf = buffer_of_platform_bytes(mlpub, &mlpub_len);
    uint8_t* mlprv_buf = NULL;
    if (mlp_buf == NULL || mlg_buf == NULL || mlpub_buf == NULL) {
      failure = "ocaml_dh_set_key: malformed bytes";
      goto bailout;
    }

    p = BN_bin2bn(mlp_buf, mlp_len, NULL);
    g = BN_bin2bn(mlg_buf, mlg_len, NULL);
    pub = BN_bin2bn(mlpub_buf, mlpub_len, NULL);

    if (Is_block(mlprv)) {
        CAMLlocal1(prvdata);

        prvdata = Field(mlprv, 0);
        mlprv_buf = buffer_of_platform_bytes(prvdata, &mlprv_len);
        if (mlprv_buf == NULL) {
          failure = "ocaml_dh_set_key: malformed bytes";
          goto bailout;
        }
        prv = BN_bin2bn(mlprv_buf, mlprv_len, NULL);
    }

    if (p == NULL || g == NULL) {
      failure = "cannot allocate internal structure for parameters";
      goto bailout;
    }

    if (pub == NULL || (Is_block(mlprv) && prv == NULL)) {
      failure = "cannot allocate internal structure for keys";
      goto bailout;
    }

    DH_set0_pqg(dh, p, NULL, g);
    DH_set0_key(dh, pub, prv);

    free(mlp_buf);
    free(mlg_buf);
    free(mlpub_buf);
    if (mlprv_buf != NULL)
      free(mlprv_buf);

    CAMLreturn(Val_unit);

 bailout:
    if (p   != NULL) BN_clear_free(p);
    if (g   != NULL) BN_clear_free(g);
    if (pub != NULL) BN_clear_free(pub);
    if (prv != NULL) BN_clear_free(prv);
    if (mlp_buf != NULL) free(mlp_buf);
    if (mlg_buf != NULL) free(mlg_buf);
    if (mlpub_buf != NULL) free(mlpub_buf);
    if (mlprv_buf != NULL) free(mlprv_buf);

    caml_failwith(failure);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dh_compute(value mldh, value mlopub) {
    DH *dh = NULL;
    BIGNUM *opub = NULL;

    CAMLparam2(mldh, mlopub);
    CAMLlocal1(output);

    if ((dh = DH_val(mldh)) == NULL)
        caml_failwith("DH has been disposed");

    const BIGNUM *b_pub, *b_prv;
    DH_get0_key(dh, &b_pub, &b_prv);

    if (b_prv == NULL)
        caml_failwith("DH:compute_key: missing keys");

    opub = BN_bin2bn((uint8_t*) String_val(mlopub), caml_string_length(mlopub), NULL);

    if (opub == NULL)
        caml_failwith("DH:compute_key: cannot allocate structure for public key");

    output = caml_alloc_string(DH_size(dh));

    if (DH_compute_key((uint8_t*) String_val(output), opub, dh) < 0) {
        BN_free(opub);
        caml_failwith("DH:compute_key: DH_compute_key failed");
    }

    BN_free(opub);

    CAMLreturn(output);
}

/* -------------------------------------------------------------------- */
#define EC_METHOD_val(v) (*((const EC_METHOD**) Data_custom_val(v)))

static struct custom_operations method_ops = {
  .identifier  = "ocaml_ec_method",
  .finalize    = custom_finalize_default,
  .compare     = custom_compare_default,
  .hash        = custom_hash_default,
  .serialize   = custom_serialize_default,
  .deserialize = custom_deserialize_default,
};

#define EC_METHOD_GEN(X) \
  CAMLprim value ocaml_##X##_method(value unit) { \
      CAMLparam1(unit);                         \
      CAMLlocal1(aout);                         \
                                                \
      aout = caml_alloc_custom(&method_ops, sizeof(EC_METHOD*), 0, 1); \
      EC_METHOD_val(aout) = EC_##X##_method();                 \
                                                \
      CAMLreturn(aout);                         \
  }

/* EC_METHOD_GEN(GFp_nistp521) */
/* EC_METHOD_GEN(GFp_nistp256) */
EC_METHOD_GEN(GFp_simple)
EC_METHOD_GEN(GFp_mont)
EC_METHOD_GEN(GFp_nist)


/* -------------------------------------------------------------------- */
#define EC_GROUP_val(v) (*((EC_GROUP**) Data_custom_val(v)))

static void ocaml_ec_group_finalize(value mlgroup) {
    EC_GROUP *group = EC_GROUP_val(mlgroup);

    if (group != NULL)
        EC_GROUP_free(group);
}

static struct custom_operations group_ops = {
  .identifier  = "ocaml_ec_group",
  .finalize    = ocaml_ec_group_finalize,
  .compare     = custom_compare_default,
  .hash        = custom_hash_default,
  .serialize   = custom_serialize_default,
  .deserialize = custom_deserialize_default,
};

CAMLprim value ocaml_ec_group_new_by_curve_name(value mlname) {
    CAMLparam1(mlname);
    CAMLlocal1(aout);

    int nid = OBJ_txt2nid(String_val(mlname));
    if (nid == NID_undef)
      caml_failwith("ocaml_ec_group_new_by_curve_name: invalid name");

    aout = caml_alloc_custom(&group_ops, sizeof(EC_GROUP*), 0, 1);
    EC_GROUP_val(aout) = EC_GROUP_new_by_curve_name(nid);

    CAMLreturn(aout);
}

/* -------------------------------------------------------------------- */
#define EC_POINT_val(v) (*((EC_POINT**) Data_custom_val(v)))

static void ocaml_ec_point_finalize(value mlpoint) {
    EC_POINT *point = EC_POINT_val(mlpoint);

    if (point != NULL)
        EC_POINT_free(point);
}

static struct custom_operations point_ops = {
  .identifier  = "ocaml_ec_point",
  .finalize    = ocaml_ec_point_finalize,
  .compare     = custom_compare_default,
  .hash        = custom_hash_default,
  .serialize   = custom_serialize_default,
  .deserialize = custom_deserialize_default,
};

CAMLprim value ocaml_ec_point_new(value mlgroup) {
    CAMLparam1(mlgroup);
    CAMLlocal1(aout);

    EC_GROUP* group = EC_GROUP_val(mlgroup);

    aout = caml_alloc_custom(&point_ops, sizeof(EC_POINT*), 0, 1);
    EC_POINT_val(aout) = EC_POINT_new(group);

    CAMLreturn(aout);
}

CAMLprim value ocaml_ec_group_set_point_conversion_form(value mlgroup, value mlcomp) {
  CAMLparam2(mlgroup, mlcomp);

  EC_GROUP* group = EC_GROUP_val(mlgroup);
  int compression = Val_int(mlcomp);
  if (compression)
    EC_GROUP_set_point_conversion_form(group, POINT_CONVERSION_COMPRESSED);
  else
    EC_GROUP_set_point_conversion_form(group, POINT_CONVERSION_UNCOMPRESSED);

  CAMLreturn(Val_unit);
}

CAMLprim value ocaml_ec_point_set_affine_coordinates_GFp(value mlgroup, value mlpoint, value mlx, value mly) {
  CAMLparam4(mlgroup, mlpoint, mlx, mly);

  EC_GROUP* group = EC_GROUP_val(mlgroup);
  EC_POINT* point = EC_POINT_val(mlpoint);
  BIGNUM* x = BN_bin2bn((uint8_t*) String_val(mlx), caml_string_length(mlx), NULL);
  BIGNUM* y = BN_bin2bn((uint8_t*) String_val(mly), caml_string_length(mly), NULL);

  EC_POINT_set_affine_coordinates_GFp(group, point, x, y, NULL);

  BN_free(x);
  BN_free(y);

  CAMLreturn(Val_unit);
}

CAMLprim value ocaml_ec_point_get_affine_coordinates_GFp(value mlgroup, value mlpoint) {
  CAMLparam2(mlgroup, mlpoint);

  EC_GROUP* group = EC_GROUP_val(mlgroup);
  EC_POINT* point = EC_POINT_val(mlpoint);
  BIGNUM* x = BN_new();
  BIGNUM* y = BN_new();
  if (x == NULL || y == NULL)
    caml_failwith("ocaml_ec_point_get_affine_coordinates_GFp: BN_new failed");

  EC_POINT_get_affine_coordinates_GFp(group, point, x, y, NULL);

  value mlx = caml_alloc_string(BN_num_bytes(x));
  value mly = caml_alloc_string(BN_num_bytes(y));
  value mlret = caml_alloc_tuple(2);

  (void) BN_bn2bin(x, (uint8_t*) String_val(mlx));
  (void) BN_bn2bin(y, (uint8_t*) String_val(mly));
  Field(mlret, 0) = mlx;
  Field(mlret, 1) = mly;

  BN_free(x);
  BN_free(y);

  CAMLreturn(mlret);
}

CAMLprim value ocaml_ec_point_is_on_curve(value mlgroup, value mlpoint) {
  CAMLparam2(mlgroup, mlpoint);

  EC_GROUP* group = EC_GROUP_val(mlgroup);
  EC_POINT* point = EC_POINT_val(mlpoint);

  CAMLreturn(Val_int(EC_POINT_is_on_curve(group, point, NULL)));
}

/* -------------------------------------------------------------------- */
#define EC_KEY_val(v) (*((EC_KEY**) Data_custom_val(v)))

static void ocaml_ec_key_finalize(value mlkey) {
    EC_KEY *key = EC_KEY_val(mlkey);

    if (key != NULL)
        EC_KEY_free(key);
}

static struct custom_operations key_ops = {
  .identifier  = "ocaml_ec_key",
  .finalize    = ocaml_ec_key_finalize,
  .compare     = custom_compare_default,
  .hash        = custom_hash_default,
  .serialize   = custom_serialize_default,
  .deserialize = custom_deserialize_default,
};

CAMLprim value ocaml_ec_key_new_by_curve_name(value mlname) {
    CAMLparam1(mlname);
    CAMLlocal1(aout);

    int nid = OBJ_txt2nid(String_val(mlname));
    if (nid == NID_undef)
      caml_failwith("ocaml_ec_key_new_by_curve_name: invalid name");

    aout = caml_alloc_custom(&key_ops, sizeof(EC_KEY*), 0, 1);
    EC_KEY_val(aout) = EC_KEY_new_by_curve_name(nid);

    CAMLreturn(aout);
}

CAMLprim value ocaml_ec_key_generate(value mlkey) {
  CAMLparam1(mlkey);

  if (EC_KEY_generate_key(EC_KEY_val(mlkey)) != 1)
    caml_failwith("ocaml_ec_key_generate: EC_KEY_generate_key failed");

  CAMLreturn(Val_unit);
}

CAMLprim value ocaml_ec_key_get0_public_key(value mlkey) {
  CAMLparam1(mlkey);
  CAMLlocal1(aout);
  EC_KEY* k = EC_KEY_val(mlkey);
  const EC_POINT* p = EC_KEY_get0_public_key(k);
  const EC_GROUP* g = EC_KEY_get0_group(k);

  // [p] is a pointer without ownership -- copy it in our data structure.
  aout = caml_alloc_custom(&point_ops, sizeof(EC_POINT*), 0, 1);
  EC_POINT_val(aout) = EC_POINT_dup(p, g);

  CAMLreturn(aout);
}

CAMLprim value ocaml_ec_key_get0_private_key(value mlkey) {
  CAMLparam1(mlkey);
  EC_KEY* key = EC_KEY_val(mlkey);
  const BIGNUM* n = EC_KEY_get0_private_key(key);

  if (n == NULL) CAMLreturn(Val_none);

  value mln = caml_alloc_string(BN_num_bytes(n));
  (void) BN_bn2bin(n, (uint8_t*) String_val(mln));

  CAMLreturn(Val_some(mln));
}

CAMLprim value ocaml_ec_key_set_private_key(value mlkey, value mlpriv) {
  CAMLparam2(mlkey, mlpriv);
  EC_KEY* key = EC_KEY_val(mlkey);
  BIGNUM* priv = BN_bin2bn((uint8_t*) String_val(mlpriv), caml_string_length(mlpriv), NULL);

  EC_KEY_set_private_key(key, priv);
  BN_free(priv);

  CAMLreturn(Val_unit);
}

CAMLprim value ocaml_ec_key_set_public_key(value mlkey, value mlpoint) {
  CAMLparam2(mlkey, mlpoint);
  EC_KEY* key = EC_KEY_val(mlkey);
  EC_POINT* point = EC_POINT_val(mlpoint);
  EC_KEY_set_public_key(key, point);
  CAMLreturn(Val_unit);
}

CAMLprim value ocaml_ec_key_get_curve_name(value mlkey) {
  CAMLparam1(mlkey);

  EC_KEY* key;
  int nid = 0;

  if ((key = EC_KEY_val(mlkey)) == NULL)
    caml_failwith("EC_KEY has been disposed");

  const EC_GROUP* group = EC_KEY_get0_group(key);
  if (group != NULL)
    nid = EC_GROUP_get_curve_name(group);

  CAMLreturn(caml_copy_string(OBJ_nid2sn(nid)));
}

CAMLprim value ocaml_ecdh_agreement(value mlkey, value mlgroup, value mlpoint) {
  CAMLparam2(mlkey, mlpoint);

  EC_KEY* my_key = EC_KEY_val(mlkey);
  EC_POINT* peer_point = EC_POINT_val(mlpoint);
  EC_GROUP* group = EC_GROUP_val(mlgroup);

  size_t field_size = EC_GROUP_get_degree(group);
  size_t shared_secret_len = (field_size + 7) / 8;

  CAMLlocal1(mlshared_secret);
  mlshared_secret = caml_alloc_string(shared_secret_len);

  size_t olen = ECDH_compute_key((uint8_t*) String_val(mlshared_secret), shared_secret_len, peer_point, my_key, NULL);

  if (olen != caml_string_length(mlshared_secret)) {
      CAMLlocal1(mlresized_secret);
      mlresized_secret = caml_alloc_string(olen);
      memcpy(String_val(mlresized_secret), String_val(mlshared_secret), olen);
      CAMLreturn(mlresized_secret);
  }

  CAMLreturn(mlshared_secret);
}

CAMLprim value ocaml_ecdsa_sign(value mlkey, value data) {
    EC_KEY *key = NULL;
    size_t olen = 0;

    CAMLparam2(mlkey, data);
    CAMLlocal1(output);

    if ((key = EC_KEY_val(mlkey)) == NULL)
        caml_failwith("EC_KEY has been disposed");

    output = caml_alloc_string(ECDSA_size(key));
    olen = caml_string_length(output);

    ERR_clear_error();

    if (ECDSA_sign(0,             /* ignored */
                 (uint8_t*) String_val(data),
                 caml_string_length(data),
                 (uint8_t*) String_val(output),
                 (unsigned*) &olen, key) == 0) {
      unsigned long err = ERR_peek_last_error();
      char* err_string = ERR_error_string(err, NULL);
      caml_failwith(err_string);
    }

    if (olen != caml_string_length(output)) {
        CAMLlocal1(sig);

        sig = caml_alloc_string(olen);
        memcpy(String_val(sig), String_val(output), olen);
        CAMLreturn(sig);
    }

    CAMLreturn(output);
}

CAMLprim value ocaml_ecdsa_verify(value mlkey, value data, value sig) {
    CAMLparam3(mlkey, data, sig);

    EC_KEY *key = NULL;
    int rr = -1;

    if ((key = EC_KEY_val(mlkey)) == NULL)
        caml_failwith("key has been disposed");

    ERR_clear_error();

    rr = ECDSA_verify(0, /* ignored */
                    (uint8_t*) String_val(data),
                    caml_string_length(data),
                    (uint8_t*) String_val(sig),
                    caml_string_length(sig),
                    key);

    if (rr == -1) {
      unsigned long err = ERR_peek_last_error();
      char* err_string = ERR_error_string(err, NULL);
      caml_failwith(err_string);
    }

    CAMLreturn((rr > 0) ? Val_true : Val_false);
}

/* -------------------------------------------------------------------- */

static int cb(int ok, X509_STORE_CTX *ctx)
{
#ifdef DEBUG
    char buf[256];
    static int      cb_index = 0;

    printf("Starting cb #%d (ok = %d)\n", ++cb_index, ok);
    if(X509_STORE_CTX_get_error(ctx) == X509_V_OK)
    {
      printf("Callback reports no error.\n");
    }else {
      printf("Error string = '%s'\n",
        X509_verify_cert_error_string(X509_STORE_CTX_get_error(ctx)));
    }

    X509 *cur = X509_STORE_CTX_get0_cert(ctx);
    X509_NAME_oneline(X509_get_subject_name(cur),buf,256);
    printf("current_cert subject:   %s\n",buf);
    X509_NAME_oneline(X509_get_issuer_name(cur),buf,256);
    printf("current_cert issuer:    %s\n",buf);
#endif

    return(ok);
}

CAMLprim value ocaml_validate_chain(value chain, value for_signing, value hostname, value cafile) {
    CAMLparam4(chain, for_signing, hostname, cafile);

    time_t current_time;
    STACK_OF(X509) *sk;
    sk = sk_X509_new_null();
    X509* top_cert = NULL;
    char *host;

    if(chain == Val_emptylist) CAMLreturn(Val_false);
    if(hostname == Val_none) host = NULL;
    else host = String_val(Some_val(hostname));

    do {
      value head = Field(chain, 0);
      size_t len = caml_string_length(head);
      X509* x509;
      unsigned char *cert = (unsigned char*)String_val(head);
      x509 = d2i_X509(NULL, (const unsigned char**) &cert, len);
//      printf("ADDING CERT[%d]\n", (int)len);
      if(!top_cert) top_cert = x509; else sk_X509_push(sk, x509);
      chain = Field(chain, 1);
    }
    while(chain != Val_emptylist);

    X509_STORE_CTX *ctx = NULL;
    X509_STORE *store = NULL;
    X509_VERIFY_PARAM *param = NULL;

    current_time = time(NULL);
    store = X509_STORE_new();
    ctx = X509_STORE_CTX_new();
    param = X509_VERIFY_PARAM_new();
    if(!ctx || !store || !param) CAMLreturn(Val_false);

    X509_STORE_set_default_paths(store);
    X509_STORE_set_verify_cb_func(store, cb);

    struct stat sb;
    if(stat(String_val(cafile), &sb) == 0 && S_ISDIR(sb.st_mode)) {
      if (X509_STORE_load_locations(store, NULL, String_val(cafile)) != 1)
	caml_failwith("ocaml_validate_chain: failed to load CAPath");
    }
    else {
      if (X509_STORE_load_locations(store, String_val(cafile), NULL) != 1)
	caml_failwith("ocaml_validate_chain: failed to load CAFile");
    }

    // Validation parameters
    X509_VERIFY_PARAM_set_flags(param, X509_V_FLAG_USE_CHECK_TIME | X509_V_FLAG_CRL_CHECK_ALL);
    X509_VERIFY_PARAM_set_time(param, current_time);
    X509_VERIFY_PARAM_set1_host(param, host, 0);
    X509_STORE_set1_param(store, param);

    X509_STORE_CTX_init(ctx, store, top_cert, sk);

    int r = X509_verify_cert(ctx);
//    printf("X509_verify_cert() == %d [%s]\n", r, X509_verify_cert_error_string(ctx->error));

    X509_STORE_free(store);
    X509_STORE_CTX_free(ctx);
    sk_X509_free(sk);
    X509_VERIFY_PARAM_free(param);

    CAMLreturn(r==1 ? Val_true : Val_false);
}

CAMLprim value ocaml_get_key_from_cert(value c) {
  CAMLparam1(c);

  unsigned char* cert = (unsigned char*)String_val(c);
  X509* x509 = d2i_X509(NULL, (const unsigned char**) &cert, caml_string_length(c));
  if(!x509) CAMLreturn(Val_none);

  EVP_PKEY* pk = X509_get_pubkey(x509);
  if(!pk) CAMLreturn(Val_none);

  CAMLlocal4(mlkey, mlrsa, mldsa, mlec);

  switch(EVP_PKEY_base_id(pk))
  {
    case EVP_PKEY_RSA:
      mlrsa = caml_alloc_custom(&evp_rsa_ops, sizeof(RSA*), 0, 1);
      RSA* rsa = EVP_PKEY_get1_RSA(pk);
      if(!rsa) CAMLreturn(Val_none);
      (void) RSA_set_method(rsa, RSA_PKCS1_OpenSSL());
      RSA_val(mlrsa) = rsa;
      mlkey = caml_alloc(1, 0); // CertRSA
      Store_field(mlkey, 0, mlrsa);
      break;

    case EVP_PKEY_DSA:
      mldsa = caml_alloc_custom(&evp_dsa_ops, sizeof(DSA*), 0, 1);
      DSA* dsa = EVP_PKEY_get1_DSA(pk);
      if (!dsa) CAMLreturn(Val_none);
      (void) DSA_set_method(dsa, DSA_OpenSSL());
      DSA_val(mldsa) = dsa;
      mlkey = caml_alloc(1, 1); // CertDSA
      Store_field(mlkey, 0, mldsa);
      break;

    case EVP_PKEY_EC:
      mlec = caml_alloc_custom(&key_ops, sizeof(EC_KEY*), 0, 1);
      EC_KEY* eck = EVP_PKEY_get1_EC_KEY(pk);
      if(!eck) CAMLreturn(Val_none);
      EC_KEY_val(mlec) = eck;
      mlkey = caml_alloc(1, 2); // CertECDSA
      Store_field(mlkey, 0, mlec);
      break;

    default:
      CAMLreturn(Val_none);
  }

  CAMLreturn(Val_some(mlkey));
}

CAMLprim value ocaml_load_chain(value pem) {
  CAMLparam1(pem);

  char *pemfile = (char*)String_val(pem);
  BIO *bio = BIO_new_file(pemfile, "r");
  if(!bio) CAMLreturn(Val_none);

  int c = 0;
  unsigned long n = 0;
  X509 *x509, *first = NULL;

  CAMLlocal2(mlc, mlret);
  mlret = Val_emptylist;

  ERR_clear_error();

  // Try to read all x509 structs in the file
  do {
    x509 = PEM_read_bio_X509_AUX(bio, NULL, NULL, NULL);

    if(!c) first = x509;

    if(!x509)
    {
      n = ERR_peek_last_error();
      if(!c ||
	 !(ERR_GET_LIB(n) == ERR_LIB_PEM
	  && ERR_GET_REASON(n) == PEM_R_NO_START_LINE))
	CAMLreturn(Val_none);
      else break;
    }

    int len;
    unsigned char *buf = NULL;
    len = i2d_X509(x509, &buf);
    if (len < 0) CAMLreturn(Val_none); // Yes there is a leak there

    CAMLlocal1(der_cert);
    der_cert = caml_alloc_string(len);
    memcpy(String_val(der_cert), buf, len);

    mlc = caml_alloc(2, 0);
    Store_field(mlc, 0, der_cert);
    Store_field(mlc, 1, mlret);
    mlret = mlc;
  }
  while(++c);

  CAMLreturn(Val_some(mlret));
}

CAMLprim value ocaml_load_key(value pem) {
  CAMLparam1(pem);

  char *pemfile = (char*)String_val(pem);
  BIO *bio = BIO_new_file(pemfile, "r");
  if(!bio) CAMLreturn(Val_none);

  EVP_PKEY* sk = PEM_read_bio_PrivateKey(bio, NULL, NULL, NULL);
  if(!sk) CAMLreturn(Val_none);
  CAMLlocal4(mlkey, mlrsa, mldsa, mlec);

  switch(EVP_PKEY_base_id(sk))
  {
    case EVP_PKEY_RSA:
      mlrsa = caml_alloc_custom(&evp_rsa_ops, sizeof(RSA*), 0, 1);
      RSA* rsa = EVP_PKEY_get1_RSA(sk);
      if(!rsa) CAMLreturn(Val_none);
      RSA_val(mlrsa) = rsa;
      mlkey = caml_alloc(1, 0); // CertRSA
      Store_field(mlkey, 0, mlrsa);
      break;

    case EVP_PKEY_DSA:
      mldsa = caml_alloc_custom(&evp_dsa_ops, sizeof(DSA*), 0, 1);
      DSA* dsa = EVP_PKEY_get1_DSA(sk);
      if (!dsa) CAMLreturn(Val_none);
      DSA_val(mldsa) = dsa;
      mlkey = caml_alloc(1, 1); // CertDSA
      Store_field(mlkey, 0, mldsa);
      break;

    case EVP_PKEY_EC:
      mlec = caml_alloc_custom(&key_ops, sizeof(EC_KEY*), 0, 1);
      EC_KEY* eck = EVP_PKEY_get1_EC_KEY(sk);
      if(!eck) CAMLreturn(Val_none);
      EC_KEY_val(mlec) = eck;
      mlkey = caml_alloc(1, 2); // CertECDSA
      Store_field(mlkey, 0, mlec);
      break;

    default:
      CAMLreturn(Val_none);
  }

  CAMLreturn(Val_some(mlkey));
}
