module CoreCrypto

open Platform.Bytes
open FStar.HyperHeap

effect EXT (a:Type) = ST a
  (requires (fun _ -> True)) 
  (ensures (fun h0 _ h -> modifies Set.empty h0 h))

type hash_alg = | MD5 | SHA1 | SHA256 | SHA384 | SHA512
type sig_alg = | RSASIG | DSA | ECDSA
type block_cipher = | AES_128_CBC | AES_256_CBC | TDES_EDE_CBC
type aead_cipher = | AES_128_GCM | AES_256_GCM
type stream_cipher = | RC4_128
type rsa_padding = | Pad_none | Pad_PKCS1

let blockSize = function
  | TDES_EDE_CBC -> 8
  | AES_128_CBC  -> 16
  | AES_256_CBC  -> 16

let aeadKeySize = function
  | AES_128_GCM -> 16
  | AES_256_GCM -> 32

let aeadRealIVSize = function
  | AES_128_GCM -> 12
  | AES_256_GCM -> 12

let aeadTagSize = function
  | AES_128_GCM -> 16
  | AES_256_GCM -> 16

let hashSize = function
  | MD5    -> 16
  | SHA1   -> 20
  | SHA256 -> 32
  | SHA384 -> 48
  | SHA512 -> 64

type rsa_key = {
  rsa_mod : bytes;
  rsa_pub_exp : bytes;
  rsa_prv_exp : option bytes;
}

type dsa_params = { dsa_p : bytes; dsa_q : bytes; dsa_g : bytes; }
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

assume val hash : alg:hash_alg -> bytes -> Tot (h:bytes{length h = hashSize alg})
assume val hmac : alg:hash_alg -> bytes -> bytes -> Tot (h:bytes{length h = hashSize alg})

assume val block_encrypt : block_cipher -> bytes -> bytes -> bytes -> bytes
assume val block_decrypt : block_cipher -> bytes -> bytes -> bytes -> bytes
assume val aead_encrypt : (a:aead_cipher) -> (k:bytes)
  -> (iv:bytes) -> (ad:bytes) -> (p:bytes) -> EXT (lbytes (length p + aeadTagSize a))
assume val aead_decrypt : (a:aead_cipher) -> (k:bytes) 
  -> (iv:bytes) -> (ad:bytes) -> (c:bytes{length c >= aeadTagSize a}) 
  -> EXT (option (lbytes (length c - aeadTagSize a)))

type cipher_stream
assume val stream_encryptor : stream_cipher -> bytes -> cipher_stream
assume val stream_decryptor : stream_cipher -> bytes -> cipher_stream
assume val stream_process : cipher_stream -> bytes -> bytes
assume val stream_fini : cipher_stream -> unit

assume val random : l:nat -> EXT (lbytes l)

assume val rsa_gen_key : int -> rsa_key
assume val rsa_encrypt : rsa_key -> rsa_padding -> bytes -> bytes
assume val rsa_decrypt : rsa_key -> rsa_padding -> bytes -> option bytes
assume val rsa_sign : option hash_alg -> rsa_key -> bytes -> bytes
assume val rsa_verify : option hash_alg -> rsa_key -> bytes -> bytes -> bool

assume val dsa_gen_key : int -> dsa_key
assume val dsa_sign : dsa_key -> bytes -> bytes
assume val dsa_verify : dsa_key -> bytes -> bytes -> bool

assume val dh_gen_params : int -> dh_params
assume val dh_gen_key : dh_params -> dh_key
assume val dh_agreement : dh_key -> bytes -> bytes

(* type ec_prime = { ecp_prime : string; ecp_order : string; ecp_a : string; ecp_b : string; ecp_gx : string; ecp_gy : string; ecp_bytelen : int; ecp_id : bytes; } *)

type ec_curve =
     | ECC_P256
     | ECC_P384
     | ECC_P521
type ec_params = { curve: ec_curve; point_compression: bool; }
type ec_point = { ecx : bytes; ecy : bytes; }

type ec_key = {
     ec_params : ec_params;
     ec_point : ec_point;
     ec_priv : option bytes;
}

assume val ec_point_serialize: ec_point -> Tot bytes
assume val ec_is_on_curve: ec_params -> ec_point -> bool
assume val ecdh_agreement: ec_key -> ec_point -> bytes

assume val ecdsa_sign: option hash_alg -> ec_key -> bytes -> bytes
assume val ecdsa_verify: option hash_alg -> ec_key -> bytes -> bytes -> bool
assume val ec_gen_key: ec_params -> ec_key
