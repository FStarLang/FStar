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
(* our encryption module is parameterized by a "native" RSA-OAEP
   implementation, available at least for F#/.NET *)

(* I am trying to capture functional correctness, which we did not
   have with F7; otherwise most refinements can be ignored.

   I think this would require coding "events" as membership of
   increasing mutable lists, possibly too advanced for a tutorial *)

module CCA2.RSA

open FStar.BaseTypes
open FStar.List.Tot

assume type pkey
assume type skey
type bytes = list byte
type nbytes (n:nat) = b:bytes{List.Tot.length b == n}
assume val plainsize  : nat
assume val ciphersize : nat
type plain   = nbytes plainsize
type cipher  = nbytes ciphersize

type keypair = pkey * skey
assume val generated : keypair -> Tot bool

assume val gen: unit -> x:keypair{generated x}
assume val dec: skey -> cipher -> Tot (option plain)  (* this function is pure *)
assume val enc: pk:pkey -> t:plain -> c:cipher { forall sk. generated (pk, sk) ==> dec sk c=Some t }  (* functional correctness *)
assume val pkbytes: pkey -> bytes
assume val dummy: plain

