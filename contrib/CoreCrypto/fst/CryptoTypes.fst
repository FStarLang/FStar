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
