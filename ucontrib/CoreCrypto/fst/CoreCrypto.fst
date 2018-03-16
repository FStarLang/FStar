(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module CoreCrypto

open FStar.Bytes

(* ------------ Hashing ------------ *)
type hash_alg =
  | MD5
  | SHA1
  | SHA224
  | SHA256
  | SHA384
  | SHA512

let hashSize = function
  | MD5    -> 16
  | SHA1   -> 20
  | SHA224 -> 28
  | SHA256 -> 32
  | SHA384 -> 48
  | SHA512 -> 64

(* These implementations are not pure; to be upgraded! *)
assume val hash : alg:hash_alg -> bytes -> Tot (h:bytes{length h = hashSize alg})
assume val hmac : alg:hash_alg -> bytes -> bytes -> Tot (h:bytes{length h = hashSize alg})

(* Digest functions *)
assume type hash_ctx : Type0 (* SI: or assume_new_abstract_type?*)
assume val digest_create : hash_alg -> EXT hash_ctx
assume val digest_update : hash_ctx -> bytes -> EXT unit
assume val digest_final : hash_ctx -> EXT bytes

(* --------------------------- *)


type sig_alg = | RSASIG | DSA | ECDSA | RSAPSS
type block_cipher = | AES_128_CBC | AES_256_CBC | TDES_EDE_CBC
type stream_cipher = | RC4_128
type rsa_padding = | Pad_none | Pad_PKCS1

(* NB these constant functions must *exactly* match those in the
      trusted CoreCrypto.ml. We should compile them instead! *)

let blockSize = function
  | TDES_EDE_CBC -> 8
  | AES_128_CBC  -> 16
  | AES_256_CBC  -> 16

(* Authenticated Encryption for TLS.
   Note that their AAD contents depends on the protocol version. *)

type aead_cipher =
  | AES_128_GCM
  | AES_256_GCM
  | CHACHA20_POLY1305
  | AES_128_CCM   // "Counter with CBC-Message Authentication Code"
  | AES_256_CCM
  | AES_128_CCM_8 // variant with truncated 8-byte tags
  | AES_256_CCM_8

// the key materials consist of an encryption key, a static IV, and an authentication key.

let aeadKeySize = function
  | AES_128_CCM       -> 16
  | AES_128_CCM_8     -> 16
  | AES_128_GCM       -> 16
  | AES_256_CCM       -> 32
  | AES_256_CCM_8     -> 32
  | AES_256_GCM       -> 32
  | CHACHA20_POLY1305 -> 32

let aeadRealIVSize (a:aead_cipher) = 12

// the ciphertext ends with an authentication tag
let aeadTagSize = function
  | AES_128_CCM_8     ->  8
  | AES_256_CCM_8     ->  8
  | AES_128_CCM       -> 16
  | AES_256_CCM       -> 16
  | AES_128_GCM       -> 16
  | AES_256_GCM       -> 16
  | CHACHA20_POLY1305 -> 16

//16-09-12 added precise concrete spec, matching what we implement in low-level/crypto
//16-09-12 for robustness, we should at least test it when using external crypto.
assume val aead_encryptT:
  a: aead_cipher ->
  k: lbytes (aeadKeySize a) ->
  iv:lbytes (aeadRealIVSize a) ->
  ad:bytes ->
  plain:bytes ->
  GTot (lbytes (length plain + aeadTagSize a))

assume val aead_encrypt:
  a: aead_cipher ->
  k: lbytes (aeadKeySize a) ->
  iv:lbytes (aeadRealIVSize a) ->
  ad:bytes ->
  plain:bytes ->
  EXT (c:bytes {c = aead_encryptT a k iv ad plain})

assume val aead_decrypt:
  a: aead_cipher ->
  k: lbytes (aeadKeySize a) ->
  iv:lbytes (aeadRealIVSize a) ->
  ad:bytes ->
  cipher:bytes{length cipher >= aeadTagSize a} ->
  EXT (o:option (b:bytes{length b + aeadTagSize a = length cipher})
    {forall (p:bytes). cipher = aead_encryptT a k iv ad p <==> (Some? o /\ Some?.v o == p) })


type rsa_key = {
  rsa_mod : bytes;
  rsa_pub_exp : bytes;
  rsa_prv_exp : option bytes;
}

type dsa_params = {
  dsa_p : bytes;
  dsa_q : bytes;
  dsa_g : bytes;
}

type dsa_key = {
  dsa_params : dsa_params;
  dsa_public : bytes;
  dsa_private : option bytes;
}

type dh_params = {
  dh_p : bytes;
  dh_g : bytes;
  dh_q : option bytes;
  safe_prime : bool;
}

type dh_key = {
  dh_params : dh_params;
  dh_public : bytes;
  dh_private : option bytes;
}

(* TODO: revisit the Tot annotations, switch to EXT when appropriate *)

assume val block_encrypt : block_cipher -> bytes -> bytes -> bytes -> EXT bytes
assume val block_decrypt : block_cipher -> bytes -> bytes -> bytes -> EXT bytes

assume new type cipher_stream : Type0
assume val stream_encryptor : stream_cipher -> bytes -> EXT cipher_stream
assume val stream_decryptor : stream_cipher -> bytes -> EXT cipher_stream
assume val stream_process : cipher_stream -> bytes -> EXT bytes
assume val stream_fini : cipher_stream -> EXT unit

assume val random : l:nat -> EXT (lbytes l)

assume val rsa_gen_key : int -> EXT (k:rsa_key{Some? k.rsa_prv_exp})
assume val rsa_encrypt : rsa_key -> rsa_padding -> bytes -> EXT bytes
assume val rsa_decrypt : k:rsa_key{Some? k.rsa_prv_exp} -> rsa_padding -> bytes -> EXT (option bytes)
assume val rsa_sign : option hash_alg -> k:rsa_key{Some? k.rsa_prv_exp} -> pss:bool -> bytes -> EXT bytes
assume val rsa_verify : option hash_alg -> rsa_key -> pss:bool -> bytes -> bytes -> EXT bool

assume val dsa_gen_key : int -> EXT (k:dsa_key{Some? k.dsa_private})
assume val dsa_sign : option hash_alg -> k:dsa_key{Some? k.dsa_private} -> bytes -> EXT bytes
assume val dsa_verify : option hash_alg -> dsa_key -> bytes -> bytes -> Tot bool

assume val dh_gen_params : int -> EXT dh_params
assume val dh_gen_key : p:dh_params -> EXT (k:dh_key{Some? k.dh_private /\ k.dh_params = p /\ length k.dh_public <= length p.dh_p})
assume val dh_agreement : k:dh_key{Some? k.dh_private} -> bytes -> EXT bytes

(* type ec_prime = { ecp_prime : string; ecp_order : string; ecp_a : string; ecp_b : string; ecp_gx : string; ecp_gy : string; ecp_bytelen : int; ecp_id : bytes; } *)

type ec_curve =
  | ECC_P256
  | ECC_P384
  | ECC_P521
  | ECC_X25519
  | ECC_X448

(* Bytelen of field elements *)
val ec_bytelen: ec_curve -> Tot (n:nat{n <= 127})
let ec_bytelen = function
  | ECC_P256 -> 32
  | ECC_P384 -> 48
  | ECC_P521 -> 66 (* ceil(521/8) *)
  | ECC_X25519 -> 32
  | ECC_X448 -> 56

type ec_params = {
  curve: ec_curve;
  point_compression: bool;
}

type ec_point = {
  ecx : bytes;
  ecy : bytes;
}

type ec_key = {
  ec_params : ec_params;
  ec_point : ec_point;
  ec_priv : option bytes;
}

assume val ec_is_on_curve: ec_params -> ec_point -> Tot bool
assume val ecdh_agreement: k:ec_key{Some? k.ec_priv} -> ec_point -> EXT bytes

assume val ecdsa_sign: option hash_alg -> k:ec_key{Some? k.ec_priv} -> bytes -> EXT bytes
assume val ecdsa_verify: option hash_alg -> ec_key -> bytes -> bytes -> EXT bool
assume val ec_gen_key: p:ec_params
  -> EXT (k:ec_key{Some? k.ec_priv /\ k.ec_params = p /\
                  length k.ec_point.ecx = ec_bytelen k.ec_params.curve /\
                  length k.ec_point.ecy = ec_bytelen k.ec_params.curve})

//TODO: keep also abtsract OpenSSL representation for efficiency?
type key =
  | KeyRSA of rsa_key
  | KeyDSA of dsa_key
  | KeyECDSA of ec_key

// If we are careless we can cause openssl segfaults when signing or encrypting
// with keys that are missing the "private" field.
// The only has_priv keys are the ones loaded with load_key and or generated with gen_key
let has_priv : key -> Type0 = function
  | KeyRSA k -> Some? k.rsa_prv_exp
  | KeyDSA k -> Some? k.dsa_private
  | KeyECDSA k -> Some? k.ec_priv

assume val validate_chain: der_list:list bytes -> for_signing:bool -> hostname:option string -> ca_file:string -> Tot bool
assume val get_key_from_cert: bytes -> Tot (option key)
assume val hash_and_sign: k:key{has_priv k} -> hash_alg -> bytes -> Tot bytes
assume val verify_signature: key -> hash_alg -> tbs:bytes -> sigv:bytes -> Tot bool
assume val load_chain: pemfile:string -> Tot (option (list bytes))
assume val load_key: keyfile:string -> Tot (option (k:key{has_priv k}))
