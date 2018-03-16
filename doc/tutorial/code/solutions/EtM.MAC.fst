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
module EtM.MAC

open FStar.Seq
open FStar.Monotonic.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Bytes
open CoreCrypto
open EtM.CPA

module Ideal = EtM.Ideal

module HST = FStar.HyperStack.ST

type rid = HST.erid
type msg = EtM.CPA.cipher

let keysize   = 64ul
let blocksize = keysize
let macsize   = hashSize SHA1

type sha1_key = lbytes32 keysize
type tag = lbytes macsize

val sha1: bytes -> Tot (h:bytes{length h = macsize})
let sha1 b = hash SHA1 b

val hmac_sha1: sha1_key -> msg -> Tot tag
let hmac_sha1 k t =
  let x5c = byte_of_int 92 in
  let x36 = byte_of_int 54 in
  let opad = create blocksize x5c in
  let ipad = create blocksize x36 in
  let xor_key_opad = xor keysize k opad in
  let xor_key_ipad = xor keysize k ipad in
  assume (UInt.fits (Bytes.length xor_key_ipad + Bytes.length t) 32);
  sha1 (xor_key_opad @| (sha1 (xor_key_ipad @| t)))

(* ------------------------------------------------------------------------ *)

(* Type log_t defined as follows (in ulib/FStar.Monotonic.Seq.fst):
   type log_t (i:rid) (a:Type) = m_rref i (seq a) grows *)

type log_t (r:rid) = Monotonic.Seq.log_t r (msg * tag)

noeq type key =
  | Key: #region:rid -> raw:sha1_key -> log:log_t region -> key

(* CH: TODO: play with names here and for the mac spec to hide the details?
   Actually these things are very similar to the things in CPA, refactor? *)
let genPost parent h0 (k:key) h1 =
    modifies Set.empty h0 h1
  /\ extends k.region parent
  /\ HyperStack.fresh_region k.region h0 h1
  /\ contains h1 k.log
  /\ sel h1 k.log == createEmpty
  (* CH: equivalent definition makes gen fail:
         /\ (sel h1 k.log).length == 0
         can't even prove:
           assert((createEmpty #key).length == 0); *)

val keygen: parent:rid -> ST key
  (requires (fun _ -> HST.witnessed (HST.region_contains_pred parent)))
  (ensures  (genPost parent))

let keygen parent =
  let raw = random32 keysize in
  let region = new_region parent in
  let log = alloc_mref_seq region createEmpty in
  Key #region raw log

val mac: k:key -> m:msg -> ST tag
  (requires (fun h0 -> True))
  (ensures  (fun h0 t h1 ->
    (let log0 = sel h0 k.log in
     let log1 = sel h1 k.log in
       modifies_one k.region h0 h1
     /\ contains h1 k.log
     /\ log1 == snoc log0 (m, t)
     /\ witnessed (at_least (Seq.length log0) (m, t) k.log)
     /\ Seq.length log1 == Seq.length log0 + 1
        (* CH: This last condition should follow from snoc, prove lemma?
               EtM.AE.fst(136,4-158,15) *)
     )))
// BEGIN: EtMMACMac
let mac k m =
  let t = hmac_sha1 k.raw m in
  write_at_end k.log (m,t);
  t
// END: EtMMACMac

// BEGIN: EtMMACVerifyT
val verify: k:key -> m:msg -> t:tag -> ST bool
  (requires (fun h -> True))
  (ensures  (fun h0 res h1 ->
     modifies_none h0 h1 /\
     (( Ideal.uf_cma && res ) ==> mem (m,t) (sel h0 k.log))))
// END: EtMMACVerifyT

// BEGIN: EtMMACVerify
let verify k m t =
  let t' = hmac_sha1 k.raw m in
  let verified = (t = t') in
  let log = !k.log in
  let found = mem (m,t) log in
  if Ideal.uf_cma then
    verified && found
  else
    verified
// END: EtMMACVerify
