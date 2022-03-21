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
module HyE.HCCA2
open FStar.HyperStack.All
open FStar.HyperStack.ST
open HyE.Plain
open HyE.PlainPKE
open Platform.Bytes
open FStar.HyperStack

module B = Platform.Bytes
module P = HyE.Plain
module C = HyE.CCA2
module A = HyE.AE
module RSA = HyE.RSA


(* we idealize first CCA2, then AE *)

type rid = FStar.Monotonic.Seq.rid

val pkey : Type0

val access_pkraw (pk:pkey) : RSA.pkey

val skey : Type0

type p = P.t
type c = C.cipher * A.cipher //lbytes(C.ciphersize + A.ciphersize)

val keygen: parent:C.rid{HyperStack.ST.witnessed (region_contains_pred parent)} -> ML (pkey * skey)
val encrypt: pkey -> p -> ML c
val decrypt: skey -> c -> ML (option p )
