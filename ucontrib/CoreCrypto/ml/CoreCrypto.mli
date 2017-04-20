type bytes = Platform.Bytes.bytes
val string_of_bytes : bytes -> string
val bytes_of_string : string -> bytes

type hash_alg = MD5 | SHA1 | SHA224 | SHA256 | SHA384 | SHA512
type sig_alg = RSASIG | DSA | ECDSA | RSAPSS
type block_cipher = AES_128_CBC | AES_256_CBC | TDES_EDE_CBC
type stream_cipher = RC4_128
type rsa_padding = Pad_none | Pad_PKCS1

type aead_cipher = 
  | AES_128_GCM   
  | AES_256_GCM
  | CHACHA20_POLY1305 
  | AES_128_CCM
  | AES_256_CCM   
  | AES_128_CCM_8
  | AES_256_CCM_8

val string_of_hash_alg: hash_alg -> string

val blockSize : block_cipher -> Z.t
val aeadKeySize : aead_cipher -> Z.t
val aeadRealIVSize : aead_cipher -> Z.t
val aeadTagSize : aead_cipher -> Z.t
val hashSize: hash_alg -> Z.t

type rsa_key = {
  rsa_mod : bytes;
  rsa_pub_exp : bytes;
  rsa_prv_exp : bytes option;
}

type dsa_params = { dsa_p : bytes; dsa_q : bytes; dsa_g : bytes; }
type dsa_key = {
  dsa_params : dsa_params;
  dsa_public : bytes;
  dsa_private : bytes option;
}

type dh_params = {
  dh_p : bytes;
  dh_g : bytes;
  dh_q : bytes option;
  safe_prime : bool;
}
type dh_key = {
  dh_params : dh_params;
  dh_public : bytes;
  dh_private : bytes option;
}

val hash : hash_alg -> bytes -> bytes

val hmac : hash_alg -> bytes -> bytes -> bytes

(* digest functions *)
type hash_ctx
val digest_create : hash_alg -> hash_ctx 
val digest_update : hash_ctx -> bytes -> unit
val digest_final : hash_ctx -> bytes 

val block_encrypt : block_cipher -> bytes -> bytes -> bytes -> bytes
val block_decrypt : block_cipher -> bytes -> bytes -> bytes -> bytes
val aead_encrypt : aead_cipher -> bytes -> bytes -> bytes -> bytes -> bytes
val aead_decrypt : aead_cipher -> bytes -> bytes -> bytes -> bytes -> bytes option

type cipher_stream
val stream_encryptor : stream_cipher -> bytes -> cipher_stream
val stream_decryptor : stream_cipher -> bytes -> cipher_stream
val stream_process : cipher_stream -> bytes -> bytes
val stream_fini : cipher_stream -> unit

val random : Z.t -> bytes

val rsa_gen_key : Z.t -> rsa_key
val rsa_encrypt : rsa_key -> rsa_padding -> bytes -> bytes
val rsa_decrypt : rsa_key -> rsa_padding -> bytes -> bytes option
val rsa_sign : hash_alg option -> rsa_key -> bytes -> bytes
val rsa_verify : hash_alg option -> rsa_key -> bytes -> bytes -> bool

val dsa_gen_key : Z.t -> dsa_key
val dsa_sign : hash_alg option -> dsa_key -> bytes -> bytes
val dsa_verify : hash_alg option -> dsa_key -> bytes -> bytes -> bool

val dh_gen_params : Z.t -> dh_params
val dh_gen_key : dh_params -> dh_key
val dh_agreement : dh_key -> bytes -> bytes

type ec_curve =
  | ECC_P256
  | ECC_P384
  | ECC_P521
  | ECC_X25519
  | ECC_X448

val ec_bytelen: ec_curve -> Z.t

type ec_params = { curve: ec_curve; point_compression: bool; }
type ec_point = { ecx : bytes; ecy : bytes; }

type ec_key = {
  ec_params : ec_params;
  ec_point : ec_point;
  ec_priv : bytes option;
}

val ec_is_on_curve: ec_params -> ec_point -> bool
val ecdh_agreement: ec_key -> ec_point -> bytes

val ecdsa_sign: hash_alg option -> ec_key -> bytes -> bytes
val ecdsa_verify: hash_alg option -> ec_key -> bytes -> bytes -> bool
val ec_gen_key: ec_params -> ec_key

type key =
  | KeyRSA of rsa_key
  | KeyDSA of dsa_key
  | KeyECDSA of ec_key

val validate_chain: bytes list -> bool -> string option -> string -> bool
val get_key_from_cert: bytes -> key option
val maybe_hash_and_sign: key -> hash_alg option -> bytes -> bytes
val verify_signature: key -> hash_alg option -> bytes -> bytes -> bool
val load_chain: string -> (bytes list) option
val load_key: string -> key option
