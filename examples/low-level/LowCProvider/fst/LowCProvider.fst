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
module LowCProvider

open Platform.Bytes
open CoreCrypto

effect EXT (a:Type) = ST a
  (requires (fun _ -> True))
  (ensures (fun h0 _ h -> modifies_none h0 h))

assume type aead_state: Type0
assume val alg: aead_state -> GTot aead_cipher

assume val aead_create:
  a: aead_cipher ->
  k: lbytes (aeadKeySize a) -> 
  EXT (st:aead_state{alg st = a})

assume val aead_encrypt:
  st: aead_state ->
  iv:lbytes (aeadRealIVSize (alg st)) ->
  ad:bytes ->
  plain:bytes ->
  EXT (c:bytes)

assume val aead_decrypt:
  st: aead_state ->
  iv:lbytes (aeadRealIVSize (alg st)) ->
  ad:bytes ->
  cipher:bytes{length cipher >= aeadTagSize (alg st)} ->
  EXT (o:option bytes)
