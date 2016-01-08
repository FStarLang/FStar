/* -------------------------------------------------------------------- */
#include <sys/types.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>

#include <caml/alloc.h>
#include <caml/callback.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

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
        EVP_MD_CTX_destroy(ctx);
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
CAMLprim value ocaml_EVP_MD_CTX_create(value md) {
    EVP_MD_CTX *ctx = NULL;

    CAMLparam1(md);
    CAMLlocal1(mlctx);

    mlctx = caml_alloc_custom(&evp_md_ctx_ops, sizeof(EVP_MD_CTX*), 0, 1);

    if ((ctx = EVP_MD_CTX_create()) == NULL) {
        caml_failwith("cannot alloc EVP_MD_CTX structure");
        goto bailout;
    }

    if (EVP_DigestInit_ex(ctx, MD_val(md), NULL) == 0) {
        caml_failwith("cannot initialize EVP_MD_CTX structure");
        goto bailout;
    }

    MD_CTX_val(mlctx) = ctx;
    CAMLreturn(mlctx);

 bailout:
    if (ctx != NULL)
        EVP_MD_CTX_destroy(ctx);
    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_MD_CTX_fini(value mlctx) {
    EVP_MD_CTX *ctx = NULL;

    CAMLparam1(mlctx);

    if ((ctx = MD_CTX_val(mlctx)) != NULL) {
        EVP_MD_CTX_destroy(ctx);
        MD_CTX_val(mlctx) = NULL;
    }

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_MD_CTX_update(value mlctx, value mldata) {
    EVP_MD_CTX *ctx = NULL;

    CAMLparam2(mlctx, mldata);

    if ((ctx = MD_CTX_val(mlctx)) == NULL) {
        caml_invalid_argument("MD_CTX has been disposed");
        CAMLreturn(Val_unit);
    }

    EVP_DigestUpdate(ctx, String_val(mldata), caml_string_length(mldata));

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_MD_CTX_final(value mlctx) {
    EVP_MD_CTX *ctx = NULL;

    CAMLparam1(mlctx);
    CAMLlocal1(aout);

    if ((ctx = MD_CTX_val(mlctx)) == NULL) {
        caml_invalid_argument("MD_CTX has been disposed");
        CAMLreturn(Val_unit);
    }

    aout = caml_alloc_string(EVP_MD_CTX_size(ctx));
    (void) EVP_DigestFinal_ex(ctx, (uint8_t*) String_val(aout), NULL);
    EVP_MD_CTX_destroy(ctx);
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
EVP_CIPHER_GEN(rc4);

/* -------------------------------------------------------------------- */
#define CIPHER_CTX_val(v) (*((EVP_CIPHER_CTX**) Data_custom_val(v)))

static void ocaml_evp_cipher_finalize(value mlctx) {
    EVP_CIPHER_CTX *ctx = CIPHER_CTX_val(mlctx);

    if (ctx != NULL) {
        EVP_CIPHER_CTX_cleanup(ctx);
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

    if ((ctx = EVP_CIPHER_CTX_new()) == NULL) {
        caml_failwith("cannot alloc EVP_CIPHER_CTX structure");
        goto bailout;
    }

    EVP_CIPHER_CTX_init(ctx);

    // Set all parameters to NULL except the cipher type in this initial call
    // Give remaining parameters in subsequent calls (e.g. EVP_CIPHER_set_key),
    // all of which have cipher type set to NULL
    if (EVP_CipherInit_ex(ctx, CIPHER_val(cipher), NULL, NULL, NULL, Bool_val(forenc)) == 0) {
        caml_failwith("cannot initialize cipher context");
        goto bailout;
    }

    // Disable padding: total amount of data encrypted or decrypted must be a
    // multiple of the block size or an error will occur
    EVP_CIPHER_CTX_set_padding(ctx, 0);

    CIPHER_CTX_val(mlctx) = ctx;
    CAMLreturn(mlctx);

 bailout:

    if (ctx != NULL) {
        EVP_CIPHER_CTX_cleanup(ctx);
        EVP_CIPHER_CTX_free(ctx);
    }

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_fini(value mlctx) {
    EVP_CIPHER_CTX *ctx = NULL;

    CAMLparam1(mlctx);

    if ((ctx = CIPHER_CTX_val(mlctx)) != NULL) {
        EVP_CIPHER_CTX_cleanup(ctx);
        EVP_CIPHER_CTX_free(ctx);
        CIPHER_CTX_val(mlctx) = NULL;
    }

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_block_size(value mlctx) {
    EVP_CIPHER_CTX *ctx = NULL;

    CAMLparam1(mlctx);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL) {
        caml_failwith("CIPHER_CTX has been disposed");
        CAMLreturn(Val_unit);
    }

    CAMLreturn(Val_int(EVP_CIPHER_CTX_block_size(ctx)));
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_key_length(value mlctx) {
    EVP_CIPHER_CTX *ctx = NULL;

    CAMLparam1(mlctx);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL) {
        caml_failwith("CIPHER_CTX has been disposed");
        CAMLreturn(Val_unit);
    }

    CAMLreturn(Val_int(EVP_CIPHER_CTX_key_length(ctx)));
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_iv_length(value mlctx) {
    EVP_CIPHER_CTX *ctx = NULL;

    CAMLparam1(mlctx);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL) {
        caml_failwith("CIPHER_CTX has been disposed");
        CAMLreturn(Val_unit);
    }

    CAMLreturn(Val_int(EVP_CIPHER_CTX_iv_length(ctx)));
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_set_key(value mlctx, value key) {
    EVP_CIPHER_CTX *ctx = NULL;

    CAMLparam2(mlctx, key);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL) {
        caml_failwith("CIPHER_CTX has been disposed");
        CAMLreturn(Val_unit);
    }

    if (EVP_CIPHER_CTX_set_key_length(ctx, caml_string_length(key)) == 0) {
        caml_failwith("cannot set CIPHER_CTX key (set_key_length)");
        CAMLreturn(Val_unit);
    }

    if (EVP_CipherInit_ex(ctx, NULL, NULL, (uint8_t*) String_val(key), NULL, -1) == 0) {
        caml_failwith("cannot set CIPHER_CTX_key");
        CAMLreturn(Val_unit);
    }

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_set_iv(value mlctx, value iv) {
    EVP_CIPHER_CTX *ctx = NULL;

    CAMLparam2(mlctx, iv);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL) {
        caml_failwith("CIPHER_CTX has been disposed");
        CAMLreturn(Val_unit);
    }

    if(EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, caml_string_length(iv), NULL) != 1) {
        caml_failwith("cannot set CIPHER_CTX_iv_length");
        CAMLreturn(Val_unit);
    }

    if (EVP_CipherInit_ex(ctx, NULL, NULL, NULL, (uint8_t*) String_val(iv), -1) == 0) {
        caml_failwith("cannot set CIPHER_CTX_iv");
        CAMLreturn(Val_unit);
    }

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_set_tag(value mlctx, value tag) {
    EVP_CIPHER_CTX *ctx = NULL;
    int olen = 0;
    int tlen = 0;

    CAMLparam2(mlctx, tag);
    CAMLlocal1(output);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL) {
        caml_failwith("CIPHER_CTX has been disposed");
        CAMLreturn(Val_unit);
    }

    // Hardcoded tag length for AES-{128,256}-GCM, may need to be revised to
    // support other ciphers
    tlen = 16;

    if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_TAG, tlen, String_val(tag)) != 1) {
       caml_failwith("failed to set AEAD tag");
       CAMLreturn(Val_unit);
    }

    olen   = EVP_MAX_BLOCK_LENGTH;
    output = caml_alloc_string(olen);

    if ((EVP_DecryptFinal_ex(ctx, (uint8_t*) output, &olen) != 1) || (olen != 0)) {
        caml_failwith("ciphertext and/or additional data authentication failed");
        CAMLreturn(Val_unit);
    }

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_get_tag(value mlctx) {
    EVP_CIPHER_CTX *ctx = NULL;
    int olen = 0;
    int tlen = 0;

    CAMLparam1(mlctx);
    CAMLlocal2(output, tag);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL) {
        caml_failwith("CIPHER_CTX has been disposed");
        CAMLreturn(Val_unit);
    }

    olen   = EVP_MAX_BLOCK_LENGTH;
    output = caml_alloc_string(olen);

    if ((EVP_EncryptFinal_ex(ctx, (uint8_t*) output, &olen) != 1) || (olen != 0)) {
        caml_failwith("final encryption failed");
        CAMLreturn(Val_unit);
    }

    // Hardcoded tag length for AES-{128,256}-GCM, may need to be revised to
    // support other ciphers
    tlen = 16;
    tag  = caml_alloc_string(tlen);

    if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_GET_TAG, tlen, (uint8_t*) tag) != 1) {
       caml_failwith("failed to get AEAD tag");
       CAMLreturn(Val_unit);
    }

    CAMLreturn(tag);
}

/* ------------------------------------------------------------------- */
CAMLprim value ocaml_EVP_CIPHER_CTX_process(value mlctx, value data) {
    EVP_CIPHER_CTX *ctx = NULL;
    int olen = 0;

    CAMLparam2(mlctx, data);
    CAMLlocal1(output);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL) {
        caml_failwith("CIPHER_CTX has been disposed");
        CAMLreturn(Val_unit);
    }

    if (caml_string_length(data) % EVP_CIPHER_CTX_block_size(ctx) != 0) {
        caml_failwith("partial block encryption/decryption not supported");
        CAMLreturn(Val_unit);
    }

    olen   = caml_string_length(data);
    output = caml_alloc_string(olen);

    if (EVP_CipherUpdate(ctx, (uint8_t*) output, &olen, (uint8_t*) String_val(data), olen) == 0) {
        caml_failwith("encryption/decryption failed");
        CAMLreturn(Val_unit);
    }

    if ((size_t) olen != caml_string_length(data)) {
        caml_failwith("EVP_CIPHER_CTX_process(): internal error");
        CAMLreturn(Val_unit);
    }

    CAMLreturn(output);
}

CAMLprim value ocaml_EVP_CIPHER_CTX_set_additional_data(value mlctx, value data) {
    EVP_CIPHER_CTX *ctx = NULL;
    int olen = 0;

    CAMLparam2(mlctx, data);
    CAMLlocal1(output);

    if ((ctx = CIPHER_CTX_val(mlctx)) == NULL) {
        caml_failwith("CIPHER_CTX has been disposed");
        CAMLreturn(Val_unit);
    }

    olen   = caml_string_length(data);
    output = caml_alloc_string(olen);

    if (EVP_CipherUpdate(ctx, NULL, &olen, (uint8_t*) String_val(data), olen) == 0) {
        caml_failwith("failed to set additional data");
        CAMLreturn(Val_unit);
    }

    if ((size_t) olen != caml_string_length(data)) {
        caml_failwith("EVP_CIPHER_CTX_process(): internal error");
        CAMLreturn(Val_unit);
    }

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
      {
          caml_failwith("EVP_HMAC failed");
          CAMLreturn(Val_unit);
      }

    if (olen != (unsigned) EVP_MD_size(MD_val(md))) {
        caml_failwith("ocaml_EVP_HMAC(): internal error");
        CAMLreturn(Val_unit);
    }

    CAMLreturn(output);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_rand_bytes(value length) {
    CAMLparam1(length);
    CAMLlocal1(output);

    output = caml_alloc_string(Int_val(length));

    if (RAND_bytes((uint8_t*) String_val(output), Int_val(length)) == 0) {
        caml_failwith("RAND_bytes failed");
        CAMLreturn(Val_unit);
    }

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
static int RSADigest_val(value digest) {
    switch (Int_val(digest)) {
    case 0: return NID_md5;
    case 1: return NID_sha1;
    case 2: return NID_sha256;
    case 3: return NID_sha384;
    case 4: return NID_sha512;
    }

    abort();
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_rsa_new(value unit) {
    RSA *rsa = NULL;

    CAMLparam1(unit);
    CAMLlocal1(mlrsa);

    mlrsa = caml_alloc_custom(&evp_rsa_ops, sizeof(RSA*), 0, 1);

    if ((rsa = RSA_new()) == NULL) {
        caml_failwith("cannot allocated RSA structure");
        goto bailout;
    }
    (void) RSA_set_method(rsa, RSA_PKCS1_SSLeay());

    RSA_val(mlrsa) = rsa;
    CAMLreturn(mlrsa);

 bailout:
    if (rsa != NULL)
        RSA_free(rsa);
    // FIXME
    CAMLreturn(Val_unit);
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
    RSA *rsa = NULL;
    BIGNUM *bn_mlexp = NULL;

    CAMLparam2(mlsz, mlexp);
    CAMLlocal4(e, n, d, mlkey);

    if ((bn_mlexp = BN_new()) == NULL) {
      caml_failwith("RSA:genkey failed");
      CAMLreturn(Val_unit);
    }

    BN_set_word(bn_mlexp, mlexp);
    if (RSA_generate_key_ex(rsa, mlsz, bn_mlexp, NULL) != 1) {
        caml_failwith("RSA:genkey failed");
        CAMLreturn(Val_unit);
    }

    n = caml_alloc_string(BN_num_bytes(rsa->n));
    e = caml_alloc_string(BN_num_bytes(rsa->e));
    d = caml_alloc_string(BN_num_bytes(rsa->d));

    // FIXME this doesn't build a value of type [Platform.Bytes.bytes]
    (void) BN_bn2bin(rsa->n, (uint8_t*) String_val(n));
    (void) BN_bn2bin(rsa->e, (uint8_t*) String_val(e));
    (void) BN_bn2bin(rsa->d, (uint8_t*) String_val(d));

    mlkey = RSAKeyAlloc();
    RSAKey_set_mod    (mlkey, n);
    RSAKey_set_pub_exp(mlkey, e);
    RSAKey_set_prv_exp(mlkey, Val_some(d));

    BN_free(bn_mlexp);
    RSA_free(rsa);

    CAMLreturn(mlkey);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_rsa_set_key(value mlrsa, value mlkey) {
    RSA *rsa = NULL;
    BIGNUM *mod = NULL;
    BIGNUM *pub = NULL;
    BIGNUM *prv = NULL;

    CAMLparam2(mlrsa, mlkey);
    CAMLlocal3(mlmod, mlpub, mlprv);

    if ((rsa = RSA_val(mlrsa)) == NULL) {
        caml_failwith("RSA has been disposed");
        goto bailout;
    }

    if (rsa->e != NULL) BN_clear_free(rsa->e);
    if (rsa->n != NULL) BN_clear_free(rsa->n);
    if (rsa->d != NULL) BN_clear_free(rsa->d);

    mlmod = RSAKey_mod(mlkey);
    mlpub = RSAKey_pub_exp(mlkey);
    mlprv = RSAKey_pvr_exp(mlkey);

    // JP: this is wrong. [mlmod] is *not* a string, it's a record of type
    // [Platform.Bytes.bytes], so there's no way [String_val] works here. FIXME
    mod = BN_bin2bn((uint8_t*) String_val(mlmod), caml_string_length(mlmod), NULL);
    pub = BN_bin2bn((uint8_t*) String_val(mlpub), caml_string_length(mlpub), NULL);

    if (Is_block(mlprv)) {
        CAMLlocal1(prvdata);

        prvdata = Field(mlprv, 0);
        // FIXME
        prv = BN_bin2bn((uint8_t*) String_val(prvdata), caml_string_length(prvdata), NULL);
    }

    if (mod == NULL || pub == NULL || (prv == NULL && Is_block(mlprv))) {
        caml_failwith("cannot allocate internal structure for keys");
        goto bailout;
    }

    rsa->n = mod;
    rsa->e = pub;
    rsa->d = prv;

    CAMLreturn(Val_unit);

 bailout:
    if (mod != NULL) BN_clear_free(mod);
    if (pub != NULL) BN_clear_free(pub);
    if (prv != NULL) BN_clear_free(prv);

    CAMLreturn(Val_unit);
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

    if ((rsa = RSA_val(mlrsa)) == NULL) {
        caml_failwith("RSA has been disposed");
        goto bailout;
    }

    if (rsa->e == NULL || (Bool_val(mlprv) && rsa->d == NULL)) {
        caml_failwith("RSA:encrypt: missing key");
        goto bailout;
    }

    padding = RSAPadding_val(mlpadding);
    rsasz   = RSA_size(rsa);

    switch (padding) {
    case RSA_NO_PADDING   : pdsz =  0; break ;
    case RSA_PKCS1_PADDING: pdsz = 11; break ;

    default:
        abort();
    }

    if (caml_string_length(data) > (rsasz - pdsz)) {
        caml_failwith("RSA:encrypt: invalid data length");
        goto bailout;
    }

    output = caml_alloc_string(rsasz);

    enc = Bool_val(mlprv) ? &RSA_private_encrypt : &RSA_public_encrypt;

    if (enc(caml_string_length(data),
            (uint8_t*) String_val(data),
            (uint8_t*) String_val(output),
            rsa, padding) < 0)
    {
        caml_failwith("RSA:encrypt: encryption failed");
        goto bailout;
    }

    CAMLreturn(output);

bailout:
    CAMLreturn(Val_unit);
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

    if ((rsa = RSA_val(mlrsa)) == NULL) {
        caml_failwith("RSA has been disposed");
        goto bailout;
    }

    if (rsa->e == NULL || (Bool_val(mlprv) && rsa->d == NULL)) {
        caml_failwith("RSA:decrypt: missing key");
        goto bailout;
    }

    padding = RSAPadding_val(mlpadding);
    rsasz   = RSA_size(rsa);

    if (caml_string_length(data) != rsasz) {
        caml_failwith("RSA:decrypt: invalid data length");
        goto bailout;
    }

    buffer = caml_alloc_string(rsasz);

    dec = Bool_val(mlprv) ? RSA_private_decrypt : RSA_public_decrypt;

    if ((rr = dec(rsasz,
                  (uint8_t*) String_val(data),
                  (uint8_t*) String_val(buffer),
                  rsa, padding)) < 0)
    {
        caml_failwith("RSA:decrypt: decryption failed");
        goto bailout;
    }

    output = caml_alloc_string(rr);
    memcpy(String_val(output), String_val(buffer), rr);

    CAMLreturn(output);

bailout:
    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_rsa_sign(value mlrsa, value mldigest, value data) {
    RSA *rsa = NULL;
    size_t olen = 0;

    CAMLparam3(mlrsa, mldigest, data);
    CAMLlocal1(output);

    if ((rsa = RSA_val(mlrsa)) == NULL) {
        caml_failwith("RSA has been disposed");
        goto bailout;
    }

    if (rsa->e == NULL || rsa->d == NULL) {
        caml_failwith("RSA:sign: missing key");
        goto bailout;
    }

    int dig = 0;
    if (mldigest == Val_none) dig = NID_md5_sha1;
    else dig = RSADigest_val(Some_val(mldigest));

    output = caml_alloc_string(RSA_size(rsa));
    olen = caml_string_length(output);

    if (RSA_sign(dig,
                 (uint8_t*) String_val(data),
                 caml_string_length(data),
                 (uint8_t*) String_val(output),
                 (unsigned*) &olen, rsa) == 0)
    {
        caml_failwith("RSA:sign: RSA_sign failed");
        goto bailout;
    }

    if (olen != caml_string_length(output)) {
        CAMLlocal1(sig);

        sig = caml_alloc_string(olen);
        memcpy(String_val(sig), String_val(output), olen);
        CAMLreturn(sig);
    }

    CAMLreturn(output);

 bailout:
    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_rsa_verify(value mlrsa, value mldigest, value data, value sig) {
    RSA *rsa = NULL;
    int rr = -1;

    CAMLparam4(mlrsa, mldigest, data, sig);

    if ((rsa = RSA_val(mlrsa)) == NULL) {
        caml_failwith("RSA has been disposed");
        goto bailout;
    }

    if (rsa->e == NULL) {
        caml_failwith("RSA:sign: missing key");
        goto bailout;
    }

    int dig = 0;
    if (mldigest == Val_none) dig = NID_md5_sha1;
    else dig = RSADigest_val(Some_val(mldigest));

    rr = RSA_verify(dig,
                    (uint8_t*) String_val(data),
                    caml_string_length(data),
                    (uint8_t*) String_val(sig),
                    caml_string_length(sig),
                    rsa);

    CAMLreturn((rr > 0) ? Val_true : Val_false);

 bailout:
    CAMLreturn(Val_unit);
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

    if ((dsa = DSA_new()) == NULL) {
        caml_failwith("cannot allocated DSA structure");
        goto bailout;
    }

    DSA_val(mldsa) = dsa;
    CAMLreturn(mldsa);

 bailout:
    if (dsa != NULL)
        DSA_free(dsa);
    // FIXME
    CAMLreturn(Val_unit);
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
    DSA *dsa = NULL;

    CAMLparam1(size);
    CAMLlocal4(p, q, g, mlparams);

    if (DSA_generate_parameters_ex(dsa, Int_val(size), NULL, 0, NULL, NULL, NULL) != 1) {
        caml_failwith("DSA:genparams failed");
        CAMLreturn(Val_unit);
    }

    p = caml_alloc_string(BN_num_bytes(dsa->p));
    q = caml_alloc_string(BN_num_bytes(dsa->q));
    g = caml_alloc_string(BN_num_bytes(dsa->g));

    (void) BN_bn2bin(dsa->p, (uint8_t*) String_val(p));
    (void) BN_bn2bin(dsa->q, (uint8_t*) String_val(q));
    (void) BN_bn2bin(dsa->g, (uint8_t*) String_val(g));

    // FIXME this does not build proper values of type [Platform.Bytes.bytes]
    mlparams = DSAParamsAlloc();
    DSAParams_set_p(mlparams, p);
    DSAParams_set_q(mlparams, q);
    DSAParams_set_g(mlparams, g);

    DSA_free(dsa);

    CAMLreturn(mlparams);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dsa_gen_key(value mlparams) {
    DSA *dsa = NULL;

    CAMLparam1(mlparams);
    CAMLlocal3(mlp, mlq, mlg);
    CAMLlocal3(mlpub, mlprv, mlkey);

    if ((dsa = DSA_new()) == NULL) {
        caml_failwith("DSA:genkey: failed to create a DSA structure");
        goto bailout;
    }

    mlp = DSAParams_p(mlparams);
    mlq = DSAParams_q(mlparams);
    mlg = DSAParams_g(mlparams);

    dsa->p = BN_bin2bn((uint8_t*) String_val(mlp), caml_string_length(mlp), NULL);
    dsa->q = BN_bin2bn((uint8_t*) String_val(mlq), caml_string_length(mlq), NULL);
    dsa->g = BN_bin2bn((uint8_t*) String_val(mlg), caml_string_length(mlg), NULL);

    if (dsa->p == NULL || dsa->q == NULL || dsa->g == NULL) {
        caml_failwith("DSA:genkey: failed dup DSA parameters");
        goto bailout;
    }

    if (DSA_generate_key(dsa) == 0) {
        caml_failwith("DSA:genkey: DSA_generate_key failed");
        goto bailout;
    }

    mlpub = caml_alloc_string(BN_num_bytes(dsa->pub_key));
    mlprv = caml_alloc_string(BN_num_bytes(dsa->priv_key));

    (void) BN_bn2bin(dsa->pub_key , (uint8_t*) String_val(mlpub));
    (void) BN_bn2bin(dsa->priv_key, (uint8_t*) String_val(mlprv));

    // FIXME this does not build proper values of type [Platform.Bytes.bytes]
    mlkey = DSAKeyAlloc();
    DSAKey_set_params(mlkey, mlparams);
    DSAKey_set_pub   (mlkey, mlpub);
    DSAKey_set_prv   (mlkey, Val_some(mlprv));

    CAMLreturn(mlkey);

 bailout:
    if (dsa != NULL)
        DSA_free(dsa);
    CAMLreturn(Val_unit);
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

    if ((dsa = DSA_val(mldsa)) == NULL) {
        caml_failwith("DSA has been disposed");
        goto bailout;
    }

    if (dsa->p        != NULL) BN_clear_free(dsa->p);
    if (dsa->q        != NULL) BN_clear_free(dsa->q);
    if (dsa->g        != NULL) BN_clear_free(dsa->g);
    if (dsa->pub_key  != NULL) BN_clear_free(dsa->pub_key);
    if (dsa->priv_key != NULL) BN_clear_free(dsa->priv_key);

    mlp = DSAParams_p(DSAKey_params(mlkey));
    mlq = DSAParams_q(DSAKey_params(mlkey));
    mlg = DSAParams_g(DSAKey_params(mlkey));
    mlpub = DSAKey_pub(mlkey);
    mlprv = DSAKey_prv(mlkey);

    // FIXME these are not [string]s but [Platform.Bytes.bytes]s, so the use of
    // [String_val] is incorrect
    p = BN_bin2bn((uint8_t*) String_val(mlp), caml_string_length(mlp), NULL);
    q = BN_bin2bn((uint8_t*) String_val(mlq), caml_string_length(mlq), NULL);
    g = BN_bin2bn((uint8_t*) String_val(mlg), caml_string_length(mlg), NULL);

    pub = BN_bin2bn((uint8_t*) String_val(mlpub), caml_string_length(mlpub), NULL);

    if (Is_block(mlprv)) {
        CAMLlocal1(prvdata);

        prvdata = Field(mlprv, 0);
        prv = BN_bin2bn((uint8_t*) String_val(prvdata), caml_string_length(prvdata), NULL);
    }

    if (p == NULL || q == NULL || g == NULL) {
        caml_failwith("cannot allocate internal structure for parameters");
        goto bailout;

    }

    if (pub == NULL || (Is_block(mlprv) && prv == NULL)) {
        caml_failwith("cannot allocate internal structure for keys");
        goto bailout;
    }

    dsa->p = p;
    dsa->q = q;
    dsa->g = g;
    dsa->pub_key = pub;
    dsa->priv_key = prv;

    CAMLreturn(Val_unit);

 bailout:
    if (p   != NULL) BN_clear_free(p);
    if (q   != NULL) BN_clear_free(q);
    if (g   != NULL) BN_clear_free(g);
    if (pub != NULL) BN_clear_free(pub);
    if (prv != NULL) BN_clear_free(prv);

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dsa_sign(value mldsa, value data) {
    DSA *dsa = NULL;
    size_t olen = 0;


    CAMLparam2(mldsa, data);
    CAMLlocal1(output);

    if ((dsa = DSA_val(mldsa)) == NULL) {
        caml_failwith("DSA has been disposed");
        goto bailout;
    }

    if (dsa->pub_key == NULL) {
        caml_failwith("DSA keys not set");
        goto bailout;
    }

    output = caml_alloc_string(DSA_size(dsa));
    olen = caml_string_length(output);

    if (DSA_sign(0,             /* ignored */
                 (uint8_t*) String_val(data),
                 caml_string_length(data),
                 (uint8_t*) String_val(output),
                 (unsigned*) &olen, dsa) == 0)
    {
        caml_failwith("DSA:sign: DSA_sign failure");
        goto bailout;
    }

    if (olen != caml_string_length(output)) {
        CAMLlocal1(sig);

        sig = caml_alloc_string(olen);
        memcpy(String_val(sig), String_val(output), olen);
        CAMLreturn(sig);
    }

    CAMLreturn(output);

 bailout:
    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dsa_verify(value mldsa, value data, value sig) {
    DSA *dsa = NULL;
    int rr = -1;

    CAMLparam3(mldsa, data, sig);

    if ((dsa = DSA_val(mldsa)) == NULL) {
        caml_failwith("DSA has been disposed");
        goto bailout;
    }

    if (dsa->pub_key == NULL) {
        caml_failwith("DSA:verify: DSA (private) keys not set");
        goto bailout;
    }

    rr = DSA_verify(0, /* ignored */
                    (uint8_t*) String_val(data),
                    caml_string_length(data),
                    (uint8_t*) String_val(sig),
                    caml_string_length(sig),
                    dsa);

#if 0                          /* Will failed on invalid ASN.1 data */
    if (rr < 0) {
        caml_failwith("DSA:verify: DSA_verify failed");
        goto bailout;
    }
#endif

    CAMLreturn((rr > 0) ? Val_true : Val_false);

 bailout:
    CAMLreturn(Val_unit);
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

    if ((dh = DH_new()) == NULL) {
        caml_failwith("cannot allocated DH structure");
        goto bailout;
    }

    DH_val(mldh) = dh;
    CAMLreturn(mldh);

 bailout:
    if (dh != NULL)
        DH_free(dh);
    // FIXME
    CAMLreturn(Val_unit);
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
    DH *dh = NULL;

    CAMLparam1(size);
    CAMLlocal3(p, g, mlparams);

    if (DH_generate_parameters_ex(dh, Int_val(size), Int_val(gen), NULL) != 1) {
        caml_failwith("DH:genparams failed");
        CAMLreturn(Val_unit);
    }

    p = caml_alloc_string(BN_num_bytes(dh->p));
    g = caml_alloc_string(BN_num_bytes(dh->g));

    (void) BN_bn2bin(dh->p, (uint8_t*) String_val(p));
    (void) BN_bn2bin(dh->g, (uint8_t*) String_val(g));

    // FIXME p, g not proper values of type [Platform.Bytes.bytes]
    mlparams = DHParamsAlloc();
    DHParams_set_p(mlparams, p);
    DHParams_set_g(mlparams, g);
    DHParams_set_q(mlparams, Val_none);
    DHParams_set_safe(mlparams, Val_true);

    DH_free(dh);

    CAMLreturn(mlparams);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dh_params_of_string(value pem) {
    BIO *bio = NULL;
    DH  *dh  = NULL;

    CAMLparam1(pem);
    CAMLlocal3(mlp, mlg, mlparams);

    if ((bio = BIO_new_mem_buf(String_val(pem), caml_string_length(pem))) == NULL) {
        caml_failwith("DH:params_of_string");
        goto bailout;
    }

    if ((dh = PEM_read_bio_DHparams(bio, NULL, NULL, NULL)) == NULL) {
        caml_failwith("DH:params_of_string");
        goto bailout;
    }

    mlp = caml_alloc_string(BN_num_bytes(dh->p));
    mlg = caml_alloc_string(BN_num_bytes(dh->g));

    (void) BN_bn2bin(dh->p, (uint8_t*) String_val(mlp));
    (void) BN_bn2bin(dh->g, (uint8_t*) String_val(mlg));

    // FIXME: [mlp], [mlg] do not have type [Platform.Bytes.bytes]; the fields [dh_q]
    // and [safe_prime] of the [mlparams] are not set.
    mlparams = DHParamsAlloc();
    DHParams_set_p(mlparams, mlp);
    DHParams_set_g(mlparams, mlg);

    DH_free(dh);

    CAMLreturn(mlparams);

 bailout:
    //    if (bio != NULL)
    //        BIO_free(bio);
    // FIXME
    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dh_gen_key(value mlparams) {
    DH *dh = NULL;

    CAMLparam1(mlparams);
    CAMLlocal2(mlp, mlg);
    CAMLlocal3(mlpub, mlprv, mlkey);

    if ((dh = DH_new()) == NULL) {
        caml_failwith("DH:genkey: failed to create a DH structure");
        goto bailout;
    }

    mlp = DHParams_p(mlparams);
    mlg = DHParams_g(mlparams);

    // FIXME [mlp] is not a [string] but a [Platform.Bytes.bytes]; same for
    // [mlg].
    dh->p = BN_bin2bn((uint8_t*) String_val(mlp), caml_string_length(mlp), NULL);
    dh->g = BN_bin2bn((uint8_t*) String_val(mlg), caml_string_length(mlg), NULL);

    if (dh->p == NULL || dh->g == NULL) {
        caml_failwith("DH:genkey: failed dup DH parameters");
        goto bailout;
    }

    if (DH_generate_key(dh) == 0) {
        caml_failwith("DH:genkey: DH_generate_key failed");
        goto bailout;
    }

    mlpub = caml_alloc_string(BN_num_bytes(dh->pub_key));
    mlprv = caml_alloc_string(BN_num_bytes(dh->priv_key));

    (void) BN_bn2bin(dh->pub_key , (uint8_t*) String_val(mlpub));
    (void) BN_bn2bin(dh->priv_key, (uint8_t*) String_val(mlprv));

    // FIXME [mlpub] and [mlprv] are not proper values of type
    // [Platform.Bytes.bytes]
    mlkey = DHKeyAlloc();
    DHKey_set_params(mlkey, mlparams);
    DHKey_set_pub   (mlkey, mlpub);
    DHKey_set_prv   (mlkey, Val_some(mlprv));

    CAMLreturn(mlkey);

 bailout:
    if (dh != NULL)
        DH_free(dh);
    // FIXME
    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dh_set_key(value mldh, value mlkey) {
    DH *dh = NULL;
    BIGNUM *p = NULL;
    BIGNUM *g = NULL;
    BIGNUM *pub = NULL;
    BIGNUM *prv = NULL;

    CAMLparam2(mldh, mlkey);
    CAMLlocal4(mlp, mlg, mlpub, mlprv);

    if ((dh = DH_val(mldh)) == NULL) {
        caml_failwith("DH has been disposed");
        goto bailout;
    }

    if (dh->p        != NULL) BN_clear_free(dh->p);
    if (dh->g        != NULL) BN_clear_free(dh->g);
    if (dh->pub_key  != NULL) BN_clear_free(dh->pub_key);
    if (dh->priv_key != NULL) BN_clear_free(dh->priv_key);

    mlp = DHParams_p(DHKey_params(mlkey));
    mlg = DHParams_g(DHKey_params(mlkey));
    mlpub = DHKey_pub(mlkey);
    mlprv = DHKey_prv(mlkey);

    // FIXME [mlp] and [mlg] do not have type [string]
    p = BN_bin2bn((uint8_t*) String_val(mlp), caml_string_length(mlp), NULL);
    g = BN_bin2bn((uint8_t*) String_val(mlg), caml_string_length(mlg), NULL);

    // FIXME [mlpub] does not have type string
    pub = BN_bin2bn((uint8_t*) String_val(mlpub), caml_string_length(mlpub), NULL);

    if (Is_block(mlprv)) {
        CAMLlocal1(prvdata);

        prvdata = Field(mlprv, 0);
        // FIXME: [prvdata] does not have type [string]
        prv = BN_bin2bn((uint8_t*) String_val(prvdata), caml_string_length(prvdata), NULL);
    }

    if (p == NULL || g == NULL) {
        caml_failwith("cannot allocate internal structure for parameters");
        goto bailout;

    }

    if (pub == NULL || (Is_block(mlprv) && prv == NULL)) {
        caml_failwith("cannot allocate internal structure for keys");
        goto bailout;
    }

    dh->p = p;
    dh->g = g;
    dh->pub_key = pub;
    dh->priv_key = prv;

    CAMLreturn(Val_unit);

 bailout:
    if (p   != NULL) BN_clear_free(p);
    if (g   != NULL) BN_clear_free(g);
    if (pub != NULL) BN_clear_free(pub);
    if (prv != NULL) BN_clear_free(prv);

    CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value ocaml_dh_compute(value mldh, value mlopub) {
    DH *dh = NULL;
    BIGNUM *opub = NULL;

    CAMLparam2(mldh, mlopub);
    CAMLlocal1(output);

    if ((dh = DH_val(mldh)) == NULL) {
        caml_failwith("DH has been disposed");
        goto bailout;
    }

    if (dh->priv_key == NULL) {
        caml_failwith("DH:compute_key: missing keys");
        goto bailout;
    }

    opub = BN_bin2bn((uint8_t*) String_val(mlopub), caml_string_length(mlopub), NULL);

    if (opub == NULL) {
        caml_failwith("DH:compute_key: cannot allocate structure for public key");
        goto bailout;
    }

    output = caml_alloc_string(DH_size(dh));

    if (DH_compute_key((uint8_t*) String_val(output), opub, dh) < 0) {
        caml_failwith("DH:compute_key: DH_compute_key failed");
        goto bailout;
    }

    BN_free(opub);

    CAMLreturn(output);

 bailout:
    if (opub != NULL)
        BN_free(opub);

    CAMLreturn(Val_unit);

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

  value mln = caml_alloc_string(BN_num_bytes(n));
  (void) BN_bn2bin(n, (uint8_t*) String_val(mln));

  CAMLreturn(mln);
}
