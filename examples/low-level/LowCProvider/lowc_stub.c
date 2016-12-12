#include <sys/types.h>
#include <sys/stat.h>
#include <stdio.h>
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

#include "tmp/Prims.h"
#include "tmp/Crypto_Config.h"
#include "tmp/Crypto_Indexing.h"
#include "tmp/Crypto_Symmetric_Bytes.h"
#include "tmp/Crypto_Symmetric_PRF.h"
#include "tmp/Crypto_Symmetric_UF1CMA.h"
#include "tmp/Crypto_AEAD_Invariant.h"
#include "tmp/Crypto_AEAD.h"

typedef Crypto_Symmetric_PRF_state____ PRF_ST;
typedef Crypto_AEAD_Invariant_state_______ AEAD_ST;
typedef Crypto_Indexing_id ID;

typedef struct {
        AEAD_ST *st;
        ID id;
} ST;

#define ST_val(v) (*((ST**) Data_custom_val(v)))

static value Val_some(value mlvalue) {
    CAMLparam1(mlvalue);
    CAMLlocal1(aout);

    aout = caml_alloc(1, 0);
    Store_field(aout, 0, mlvalue);

    CAMLreturn(aout);
}

#define Val_none Val_int(0)

static void ocaml_ST_finalize(value st) {
    ST* s = ST_val(st);

    if(s != NULL) {
        AEAD_ST *st = s->st;
        if(st != NULL) {
                // Free PRF state
                if(&(st->x02) != NULL) free(&(st->x02));
                free(st);
        }
        free(s);
    }
}

static struct custom_operations st_ops = {
  .identifier  = "ocaml_st",
  .finalize    = ocaml_ST_finalize,
  .compare     = custom_compare_default,
  .hash        = custom_hash_default,
  .serialize   = custom_serialize_default,
  .deserialize = custom_deserialize_default,
};

CAMLprim value ocaml_AEAD_create(value alg, value key) {
        CAMLparam2(alg, key);
        Crypto_Indexing_cipherAlg calg;
        switch(Int_val(alg)){
                case 0:
                        calg = Crypto_Indexing_aeadAlg_AES_128_GCM;
                        break;
                case 1:
                        calg = Crypto_Indexing_aeadAlg_AES_256_GCM;
                        break;
                case 2:
                        calg = Crypto_Indexing_aeadAlg_CHACHA20_POLY1305;
                        break;
                default:
                        caml_failwith("LowCProvider: unsupported AEAD alg");
        }
        Crypto_Indexing_id id = {.cipher = calg, .aes=Crypto_Config_aesImpl_SpartanAES, .uniq = 0};
        uint8_t* ckey = (uint8_t*) String_val(key);
        uint32_t keylen = caml_string_length(key);

        uint8_t *keystate = calloc(Crypto_Symmetric_PRF_statelen(id), sizeof (uint8_t));
        Crypto_Symmetric_Cipher_init(id, ckey, keystate);
  
        PRF_ST* prf = malloc(sizeof(PRF_ST));

        prf->x00 = FStar_HyperHeap_root;
        prf->x01 = FStar_HyperHeap_root;
        prf->x02 = keystate;
        prf->x03 = (Crypto_Symmetric_PRF_no_table(id, FStar_HyperHeap_root, FStar_HyperHeap_root), (void *)0);

        void *log = FStar_ST_ralloc(FStar_HyperHeap_root, FStar_Seq_createEmpty((uint8_t )0));
        Prims_option__uint8_t_ ak;

        if (Crypto_Symmetric_UF1CMA_skeyed(id))
        {
                Crypto_Symmetric_PRF_domain____ x = { .iv = FStar_Int_Cast_uint64_to_uint128((uint64_t )0), .ctr = (uint32_t )0 };
                uint8_t *keyBuffer = calloc(Crypto_Symmetric_UF1CMA_skeylen(id), sizeof (uint8_t ));
                Crypto_Symmetric_PRF_getBlock(id, *prf, x, Crypto_Symmetric_UF1CMA_skeylen(id), keyBuffer);
    
                ak = (Prims_option__uint8_t_ ){
                        .tag = Prims_option__uint8_t__Some,
                                { .case_Some = { .v = keyBuffer } }
                };
        }
        else
                ak = (Prims_option__uint8_t_ ){ .tag = Prims_option__uint8_t__None, { .case_None = {  } } };

        AEAD_ST* st = malloc(sizeof(AEAD_ST));
        st->x00 = FStar_HyperHeap_root;
        st->x01 = log;
        st->x02 = *prf;
        st->x03 = ak;

        ST *s = malloc(sizeof(ST));
        s->st = st;
        s->id = id;

        CAMLlocal1(mlret);
        mlret = caml_alloc_custom(&st_ops, sizeof(ST*), 0, 1);
        ST_val(mlret) = s;
        CAMLreturn(mlret);
}

CAMLprim value ocaml_AEAD_encrypt(value state, value iv, value ad, value plain) {
        CAMLparam4(state, iv, ad, plain);

        ST* st = ST_val(state);
        AEAD_ST *ast = st->st;
        ID id = st->id; 
        uint8_t* civ = (uint8_t*) String_val(iv);
        FStar_UInt128_t n = Crypto_Symmetric_Bytes_load_uint128((uint32_t )caml_string_length(iv), civ);
        uint8_t* cad = (uint8_t*) String_val(ad);
        uint32_t adlen = caml_string_length(ad);
        uint8_t* cplain = (uint8_t*) String_val(plain);
        uint32_t plainlen = caml_string_length(plain);

        CAMLlocal1(cipher);
        // ADL: hardcoded taglen here TODO
        cipher = caml_alloc_string(plainlen + 16);
        uint8_t* ccipher = (uint8_t*) String_val(cipher);
        for (uint32_t i = 0; i < plainlen + 16; ++i)
          ccipher[i] = (uint8_t )0;

        Crypto_AEAD_encrypt(id, *ast, n, adlen, cad, plainlen, cplain, ccipher);
        CAMLreturn(cipher);
}

CAMLprim value ocaml_AEAD_decrypt(value state, value iv, value ad, value cipher) {
        CAMLparam4(state, iv, ad, cipher);

        ST* st = ST_val(state);
        AEAD_ST *ast = st->st;
        ID id = st->id;
        uint8_t* civ = (uint8_t*) String_val(iv);
        FStar_UInt128_t n = Crypto_Symmetric_Bytes_load_uint128((uint32_t )caml_string_length(iv), civ);
        uint8_t* cad = (uint8_t*) String_val(ad);
        uint32_t adlen = caml_string_length(ad);
        uint8_t* ccipher = (uint8_t*) String_val(cipher);
        uint32_t cipherlen = caml_string_length(cipher);
        if(cipherlen < 16) CAMLreturn(Val_none);

        CAMLlocal1(plain);
        // ADL: hardcoded taglen here TODO
        uint32_t plainlen = cipherlen - 16;
        plain = caml_alloc_string(plainlen);
        uint8_t* cplain = (uint8_t*) String_val(plain);
        for (uint32_t i = 0; i < plainlen; ++i)
          cplain[i] = (uint8_t )0;
        
        if(Crypto_AEAD_decrypt(id, *ast, n, adlen, cad, plainlen, cplain, ccipher))
        {
                CAMLreturn(Val_some(plain));
        }
        CAMLreturn(Val_none);
}

