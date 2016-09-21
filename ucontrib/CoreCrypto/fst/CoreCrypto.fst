module CoreCrypto

open Platform.Bytes

effect EXT (a:Type) = ST a
  (requires (fun _ -> True)) 
  (ensures (fun h0 _ h -> modifies_none h0 h))

type hash_alg = | MD5 | SHA1 | SHA224 | SHA256 | SHA384 | SHA512
type sig_alg = | RSASIG | DSA | ECDSA | RSAPSS
type block_cipher = | AES_128_CBC | AES_256_CBC | TDES_EDE_CBC
type stream_cipher = | RC4_128
type rsa_padding = | Pad_none | Pad_PKCS1

let blockSize = function
  | TDES_EDE_CBC -> 8
  | AES_128_CBC  -> 16
  | AES_256_CBC  -> 16


let hashSize = function
  | MD5    -> 16
  | SHA1   -> 20
  | SHA224 -> 28
  | SHA256 -> 32
  | SHA384 -> 48
  | SHA512 -> 64



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
  | AES_128_GCM       -> 16 + 16
  | AES_256_CCM       -> 32 
  | AES_256_CCM_8     -> 32 
  | AES_256_GCM       -> 32 + 16
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
//16-09-12 for robustness, we should at least test t when using external crypto.
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
  EXT (o:option bytes {forall (p:bytes). cipher = aead_encryptT a k iv ad p ==> o = Some p })


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

assume val hash : alg:hash_alg -> bytes -> Tot (h:bytes{length h = hashSize alg})
assume val hmac : alg:hash_alg -> bytes -> bytes -> Tot (h:bytes{length h = hashSize alg})

(* Digest functions *)
assume type hash_ctx : Type0 (* SI: or assume_new_abstract_type?*)
assume val digest_create : hash_alg -> hash_ctx
assume val digest_update : hash_ctx -> bytes -> unit 
assume val digest_final : hash_ctx -> bytes  

assume val block_encrypt : block_cipher -> bytes -> bytes -> bytes -> Tot bytes
assume val block_decrypt : block_cipher -> bytes -> bytes -> bytes -> Tot bytes

assume new type cipher_stream : Type0
assume val stream_encryptor : stream_cipher -> bytes -> EXT cipher_stream
assume val stream_decryptor : stream_cipher -> bytes -> EXT cipher_stream
assume val stream_process : cipher_stream -> bytes -> EXT bytes
assume val stream_fini : cipher_stream -> EXT unit

assume val random : l:nat -> EXT (lbytes l)

assume val rsa_gen_key : int -> EXT rsa_key
assume val rsa_encrypt : rsa_key -> rsa_padding -> bytes -> EXT bytes
assume val rsa_decrypt : rsa_key -> rsa_padding -> bytes -> Tot (option bytes)
assume val rsa_sign : option hash_alg -> rsa_key -> bytes -> EXT bytes
assume val rsa_verify : option hash_alg -> rsa_key -> bytes -> bytes -> Tot bool

assume val dsa_gen_key : int -> EXT dsa_key
assume val dsa_sign : option hash_alg -> dsa_key -> bytes -> EXT bytes
assume val dsa_verify : option hash_alg -> dsa_key -> bytes -> bytes -> Tot bool

assume val dh_gen_params : int -> EXT dh_params
assume val dh_gen_key : p:dh_params
  -> Tot (k:dh_key{k.dh_params = p /\ length k.dh_public <= length p.dh_p})
assume val dh_agreement : dh_key -> bytes -> Tot bytes

(* type ec_prime = { ecp_prime : string; ecp_order : string; ecp_a : string; ecp_b : string; ecp_gx : string; ecp_gy : string; ecp_bytelen : int; ecp_id : bytes; } *)

type ec_curve =
  | ECC_P256
  | ECC_P384
  | ECC_P521

(* Bytelen of field elements *)
val ec_bytelen: ec_curve -> Tot int
let ec_bytelen = function
  | ECC_P256 -> 32
  | ECC_P384 -> 48
  | ECC_P521 -> 66 (* ceil(521/8) *)

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
assume val ecdh_agreement: ec_key -> ec_point -> Tot bytes

assume val ecdsa_sign: option hash_alg -> ec_key -> bytes -> EXT bytes
assume val ecdsa_verify: option hash_alg -> ec_key -> bytes -> bytes -> Tot bool
assume val ec_gen_key: p:ec_params
  -> Tot (k:ec_key{k.ec_params = p /\
                  length k.ec_point.ecx = ec_bytelen k.ec_params.curve /\
                  length k.ec_point.ecy = ec_bytelen k.ec_params.curve})

//TODO: keep also abtsract OpenSSL representation for efficiency?
type key =
  | KeyRSA of rsa_key
  | KeyDSA of dsa_key
  | KeyECDSA of ec_key

assume val validate_chain: der_list:list bytes -> for_signing:bool -> hostname:option string -> ca_file:string -> Tot bool
assume val get_key_from_cert: bytes -> Tot (option key)
assume val hash_and_sign: key -> hash_alg -> bytes -> Tot bytes
assume val verify_signature: key -> hash_alg -> tbs:bytes -> sigv:bytes -> Tot bool
assume val load_chain: pemfile:string -> Tot (option (list bytes))
assume val load_key: keyfile:string -> Tot (option key)
