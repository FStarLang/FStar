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
