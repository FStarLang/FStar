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
module RSA (* trustedd implementation of RSA-OAEP *) 
open Array

assume type pkey
assume type skey
type bytes = seq byte
type nbytes (n:nat) = b:bytes{length b == n}
assume val plainsize  : nat
assume val ciphersize : nat
type plain  = nbytes plainsize
type cipher = nbytes ciphersize

type keypair = pkey * skey                         
assume val generated : keypair -> Tot bool

assume val gen: unit -> x:keypair{generated x}
assume val dec: skey -> cipher -> Tot (option plain)  (* this function is pure *) 
assume val enc: pk:pkey -> t:plain -> c:cipher { forall sk. generated (pk, sk) ==> dec sk c=Some t }  (* functional correctness *) 
assume val pkbytes: pkey -> bytes
assume val dummy: plain 

module PKE (* same as in PKE, except for the plaintext type *) 

type plain = SymEnc.key
type r = AES.key
type cipher = RSA.cipher

assume val ideal: bool

val ciphersize: nat
let ciphersize = RSA.ciphersize

val repr: key:plain { not ideal } -> Tot r
let repr = SymEnc.keyrepr 

assume type skey
assume type pkey

assume val keygen: unit -> pkey * skey
assume val encrypt: pkey -> plain -> cipher
assume val decrypt: skey -> cipher -> option plain


module Hybrid
open Array
type bytes = seq byte
type nbytes (n:nat) = b:bytes{length b == n}

(* we idealize first PKE, then SymEnc *)

type pkey = PKE.pkey
type skey = PKE.skey
type p = SymEnc.p
type c = nbytes (PKE.ciphersize + AES.ciphersize)

val keygen: unit -> pkey * skey
val encrypt: pkey -> p -> c 
val decrypt: skey -> c -> option p 


let keygen() = PKE.keygen() 

let encrypt pk t = 
  let k = SymEnc.keygen true in 
  append (PKE.encrypt pk k) (SymEnc.encrypt k t)

let decrypt sk c =
  let (c0,c1) = split c PKE.ciphersize in 
  match PKE.decrypt sk c0 with 
  | Some k -> SymEnc.decrypt k c1
  | None   -> None
