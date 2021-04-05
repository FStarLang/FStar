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
module HyE.CCA2  (* intuitively, parameterized by both PlainPKE and RSA *)
open FStar.HyperStack.All
open FStar.HyperStack.ST
open FStar.HyperStack
open FStar.Seq
open FStar.Monotonic.Seq

open FStar.List.Tot
open HyE.PlainPKE
module RSA = HyE.RSA
module PlainPKE = HyE.PlainPKE

type rid = erid
type cipher = RSA.cipher
noeq type entry =
  | Entry : c:RSA.cipher
         -> p:PlainPKE.t
         -> entry

val ciphersize : nat

type log_t (r:rid) = m_rref r (seq entry) grows

val pkey : Type0

val access_pk_raw (pk:pkey) : RSA.pkey

val skey : Type0

val keygen: parent:rid{HyperStack.ST.witnessed (region_contains_pred parent)} -> ML (pkey * skey)

val encrypt (pk:pkey) (p:PlainPKE.t) : ML RSA.cipher

val decrypt (sk:skey) (c:RSA.cipher) : ML (option (PlainPKE.t))
