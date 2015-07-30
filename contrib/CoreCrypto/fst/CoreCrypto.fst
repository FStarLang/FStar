(* STATUS : JK : added a dummy DHDB interface needed by the DHDBManager, needs implementation *)

module CoreCrypto
open Platform.Bytes

type hash_alg = | MD5 | SHA1 | SHA256 | SHA384 | SHA512
type sig_alg = | RSASIG | DSA | ECDSA
type block_cipher = | AES_128_CBC | AES_256_CBC | TDES_EDE_CBC
type aead_cipher = | AES_128_GCM | AES_256_GCM
type stream_cipher = | RC4_128
type rsa_padding = | Pad_none | Pad_PKCS1

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

assume val hash : hash_alg -> bytes -> bytes
assume val hmac : hash_alg -> bytes -> bytes -> bytes

assume val block_encrypt : block_cipher -> bytes -> bytes -> bytes -> bytes
assume val block_decrypt : block_cipher -> bytes -> bytes -> bytes -> bytes
assume val aead_encrypt : aead_cipher -> bytes -> bytes -> bytes -> bytes -> Tot 'a
//should become St 'a
assume val aead_decrypt : aead_cipher -> bytes -> bytes -> bytes -> bytes -> Tot 'a
//should become St 'a

type cipher_stream
assume val stream_encryptor : stream_cipher -> bytes -> cipher_stream
assume val stream_decryptor : stream_cipher -> bytes -> cipher_stream
assume val stream_process : cipher_stream -> bytes -> bytes
assume val stream_fini : cipher_stream -> unit

assume val random : l:nat -> lbytes l

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
