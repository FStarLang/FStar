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
module HyE.AE
open FStar.HyperStack.ST
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.HyperStack
open HyE.Ideal

open Platform.Bytes
open CoreCrypto
module CC = CoreCrypto
module B = Platform.Bytes

open HyE.Plain
module Plain = HyE.Plain

noeq type key : Type0 =
  | Key: #region:erid -> raw:aes_key -> log:mlog_t region -> key

let key_region (k:key) :erid = k.region

let key_log (k:key) :mlog_t (key_region k) = k.log

let keygen parent =
  let raw = random keysize in
  let region = new_region parent in
  let log = alloc_mref_seq region Seq.empty in
  Key #region raw log

let leak k = k.raw

let encrypt k m =
  recall k.log;
  let iv = random ivsize in
  let text = if ind_cca && int_ctxt then createBytes (length m) 0z else repr m in
  let c = CC.aead_encrypt AES_128_GCM k.raw iv empty_bytes text in
  let c = iv@|c in
  write_at_end k.log (m,c);
  c

let decrypt k c =
  if int_ctxt then
    let log = !k.log in
    match seq_find (fun mc -> snd mc = c) log with
    | Some mc -> Some (fst mc)
    | None -> None
  else
    let iv,c' = split c ivsize in
    assume( B.length c' >= aeadTagSize AES_128_GCM);
    let poption = (CC.aead_decrypt AES_128_GCM k.raw iv empty_bytes c') in
    if Some? poption then
      Some (coerce (Some?.v poption))
    else
      None
