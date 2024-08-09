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
module Crypto.Indexing

open Crypto.Config

(**
This module defines the type of indexes and helper functions.
An application built on the Crypto namespace should re-implement this module to suit its own indexing practices.

(see mitls-fstar/src/tls/Crypto.Index.fst)
**)

type rw = | Reader | Writer

type macAlg =
  | POLY1305
  | GHASH

type cipherAlg =
  | AES128
  | AES256
  | CHACHA20

// References:
//  - RFC 7539 for the AEAD algorithm
//  - RFC 7905 for ChaCha20_Poly1305 TLS ciphersuites
type aeadAlg =
  | AES_128_GCM
  | AES_256_GCM
  | CHACHA20_POLY1305

abstract type id = {
  cipher: aeadAlg;
  aes: aesImpl;
  uniq: UInt32.t;
}

let aeadAlg_of_id i = i.cipher

let macAlg_of_id i =
  match i.cipher with
  | AES_128_GCM       -> GHASH
  | AES_256_GCM       -> GHASH
  | CHACHA20_POLY1305 -> POLY1305

let cipherAlg_of_id i =
  match i.cipher with
  | AES_128_GCM       -> AES128
  | AES_256_GCM       -> AES256
  | CHACHA20_POLY1305 -> CHACHA20

let aesImpl_of_id (i:id) = i.aes

let testId (a:aeadAlg) : i:id{i.cipher == a} =
  { cipher = a; aes=Crypto.Config.aes_implementation; uniq = 0ul; }
