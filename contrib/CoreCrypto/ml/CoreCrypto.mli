type bytes = Platform.Bytes.bytes
val string_of_bytes : bytes -> string
val bytes_of_string : string -> bytes

type hash_alg = MD5 | SHA1 | SHA256 | SHA384 | SHA512
type sig_alg = RSASIG | DSA | ECDSA
type block_cipher = AES_128_CBC | AES_256_CBC | TDES_EDE_CBC
type aead_cipher = AES_128_GCM | AES_256_GCM
type stream_cipher = RC4_128
type rsa_padding = Pad_none | Pad_PKCS1

val blockSize : block_cipher -> int
val aeadKeySize : aead_cipher -> int
val aeadRealIVSize : aead_cipher -> int
val aeadTagSize : aead_cipher -> int
val hashSize: hash_alg -> int

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

val block_encrypt : block_cipher -> bytes -> bytes -> bytes -> bytes
val block_decrypt : block_cipher -> bytes -> bytes -> bytes -> bytes
val aead_encrypt : aead_cipher -> bytes -> bytes -> bytes -> bytes -> bytes
val aead_decrypt : aead_cipher -> bytes -> bytes -> bytes -> bytes -> bytes option

type cipher_stream
val stream_encryptor : stream_cipher -> bytes -> cipher_stream
val stream_decryptor : stream_cipher -> bytes -> cipher_stream
val stream_process : cipher_stream -> bytes -> bytes
val stream_fini : cipher_stream -> unit

val random : int -> bytes

val rsa_gen_key : int -> rsa_key
val rsa_encrypt : rsa_key -> rsa_padding -> bytes -> bytes
val rsa_sign : hash_alg option -> rsa_key -> bytes -> bytes
val rsa_verify : hash_alg option -> rsa_key -> bytes -> bytes -> bool

val dsa_gen_key : int -> dsa_key
val dsa_sign : dsa_key -> bytes -> bytes
val dsa_verify : dsa_key -> bytes -> bytes -> bool

val dh_gen_params : int -> dh_params
val dh_gen_key : dh_params -> dh_key
val dh_agreement : dh_key -> bytes -> bytes

type ec_curve =
     | ECC_P256
     | ECC_P384
     | ECC_P521
type ec_params = { curve: ec_curve; point_compression: bool; }
type ec_point = { ecx : bytes; ecy : bytes; }

type ec_key = {
     ec_params : ec_params;
     ec_point : ec_point;
     ec_priv : bytes option;
}

val ec_point_serialize: ec_point -> bytes
val ec_is_on_curve: ec_params -> ec_point -> bool
val ecdh_agreement: ec_key -> ec_point -> bytes

val ecdsa_sign: hash_alg option -> ec_key -> bytes -> bytes
val ecdsa_verify: hash_alg option -> ec_key -> bytes -> bytes -> bool
val ec_gen_key: ec_params -> ec_key
