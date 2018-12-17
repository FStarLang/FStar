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

noeq abstract type pkey =
  | PKey: #region:rid{HyperStack.ST.witnessed (region_contains_pred region)} -> rawpk:RSA.pkey -> cca_pk:C.pkey  -> pkey

abstract let access_pkraw (pk:pkey) =
  PKey?.rawpk pk

noeq abstract type skey =
  | SKey: cca_sk:C.skey -> pk:pkey  -> skey    type p = P.t

type c = C.cipher * A.cipher //lbytes(C.ciphersize + A.ciphersize)

val keygen: parent:rid{HyperStack.ST.witnessed (region_contains_pred parent)} -> ML (pkey * skey)
val encrypt: pkey -> p -> ML c
val decrypt: skey -> c -> ML (option p )


let keygen parent =
  let cca_pk, cca_sk = C.keygen parent in
  let region = new_region parent in
  let pkey = PKey #region (C.access_pk_raw cca_pk) cca_pk in
  pkey, SKey cca_sk pkey


let encrypt pk t =
  let region = new_region pk.region in
  let k = A.keygen region in
  ((C.encrypt pk.cca_pk k) ,(A.encrypt k t))


let decrypt sk c =
  let (c0,c1) = c in
  match C.decrypt sk.cca_sk c0 with
  | Some k -> A.decrypt k c1
  | None   -> None
