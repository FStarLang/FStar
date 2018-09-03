(* Some type definitions for F* programs that extract to OCaml and then wish to
 * use LowCProvider.  *)
module CryptoTypes

type aead_cipher =
  | AES_128_GCM
  | AES_256_GCM
  | CHACHA20_POLY1305
  | AES_128_CCM   // "Counter with CBC-Message Authentication Code"
  | AES_256_CCM
  | AES_128_CCM_8 // variant with truncated 8-byte tags
  | AES_256_CCM_8

// the key materials consist of an encryption key, a static IV, and an authentication key.

let aeadKeyLen = function
  | AES_128_CCM       -> 16ul
  | AES_128_CCM_8     -> 16ul
  | AES_128_GCM       -> 16ul
  | AES_256_CCM       -> 32ul
  | AES_256_CCM_8     -> 32ul
  | AES_256_GCM       -> 32ul
  | CHACHA20_POLY1305 -> 32ul
let aeadKeySize a = UInt32.v (aeadKeyLen a)

let aeadRealIVLen (a:aead_cipher) = 12ul
let aeadRealIVSize a = UInt32.v (aeadRealIVLen a)

// the ciphertext ends with an authentication tag
let aeadTagLen = function
  | AES_128_CCM_8     ->  8ul
  | AES_256_CCM_8     ->  8ul
  | AES_128_CCM       -> 16ul
  | AES_256_CCM       -> 16ul
  | AES_128_GCM       -> 16ul
  | AES_256_GCM       -> 16ul
  | CHACHA20_POLY1305 -> 16ul
let aeadTagSize a = UInt32.v (aeadTagLen a)
