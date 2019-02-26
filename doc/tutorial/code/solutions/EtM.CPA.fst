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
module EtM.CPA

open FStar.Seq
open FStar.Monotonic.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open EtM.Ideal


open Platform.Bytes
open CoreCrypto

module B = Platform.Bytes

module HST = FStar.HyperStack.ST

open EtM.Plain

type rid = HST.erid
let ivsize = blockSize AES_128_CBC
let keysize = 16
type aes_key = lbytes keysize (* = b:bytes{B.length b = keysize} *)
type msg = plain
type cipher = b:bytes{B.length b >= ivsize}
(* MK: minimal cipher length twice blocksize? *)

type log_t (r:rid) = Monotonic.Seq.log_t r (msg * cipher)

(* CH*MK: If we wanted to also prove correctness of the EtM.AE
          we would additionally need this
type log_t (r:rid) (raw:aes_key) =
  Monotonic.Seq.log_t r (m:msg & c:cipher{
    let p = if ind_cpa then createBytes (length m) 0z else repr m in
    let (iv,c') = split c ivsize in
    c' = CoreCrypto.block_encrypt AES_128_CBC raw iv p}) *)

noeq type key =
  | Key: #region:rid -> raw:aes_key -> log:log_t region -> key

let genPost parent m0 (k:key) m1 =
    modifies Set.empty m0 m1
  /\ extends k.region parent
  /\ HyperStack.fresh_region k.region m0 m1
  /\ contains m1 k.log
  /\ sel m1 k.log == createEmpty

val keygen: parent:rid -> ST key
  (requires (fun _ -> HST.witnessed (HST.region_contains_pred parent)))
  (ensures  (genPost parent))

let keygen parent =
  let raw = random keysize in
  let region = new_region parent in
  let log = alloc_mref_seq region createEmpty in
  Key #region raw log

val encrypt: k:key -> m:msg -> ST cipher
  (requires (fun h0 -> True (* If we wanted to avoid recall:
                               contains h0 k.log *)))
  (ensures  (fun h0 c h1 ->
    (let log0 = sel h0 k.log in
     let log1 = sel h1 k.log in
      modifies_one k.region h0 h1 /\
      contains h1 k.log
     /\ log1 == snoc log0 (m, c)
     /\ witnessed (at_least (Seq.length log0) (m, c) k.log))))


// BEGIN: EtMCPAEncrypt
let encrypt k m =
  recall k.log;
  let iv = random ivsize in
  let text = if ind_cpa then createBytes (length m) 0z else repr m in
  let c = CoreCrypto.block_encrypt AES_128_CBC k.raw iv text in
  let c = iv@|c in
  write_at_end k.log (m,c);
  c
// END: EtMCPAEncrypt

(* CH*MK: If we wanted to also prove correctness of the EtM.AE
          we would additionally need this
assume val correctness : k:key -> iv:bytes -> t:bytes -> Lemma
  (CoreCrypto.block_decrypt AES_128_CBC k.raw iv
    (CoreCrypto.block_encrypt AES_128_CBC k.raw iv t) = t)

val encryption_injective : k:key -> iv:bytes -> t1:bytes -> t2:bytes -> Lemma
  (CoreCrypto.block_encrypt AES_128_CBC k.raw iv t1
 = CoreCrypto.block_encrypt AES_128_CBC k.raw iv t2 ==> t1 = t2)
let encryption_injective k iv t1 t2 = correctness k iv t1; correctness k iv t2
*)

(* this doesn't really belong here *)
val mem : #a:eqtype -> x:a -> xs:Seq.seq a -> Tot bool
let mem (#a:eqtype) x xs = Some? (Seq.seq_find (fun y -> y = x) xs)

// BEGIN: EtMCPADecryptRequires
val decrypt: k:key -> c:cipher -> ST msg
  (requires (fun h0 ->
    Map.contains (get_hmap h0) k.region /\
    (let log0 = sel h0 k.log in
      (b2t ind_cpa_rest_adv) ==> Some? (seq_find (fun mc -> snd mc = c) log0 )
    )
  ))
// END: EtMCPADecryptRequires
  (* Replace the line containing ==> with True to learn more about why CPA security 
     requires a stronger precondition *)
  (ensures  (fun h0 res h1 ->
    modifies_none h0 h1 /\
    ( (b2t ind_cpa_rest_adv) ==> mem (res,c) (sel h0 k.log)
     (* (let log0 = sel h0 k.log in *)
     (*  let found = seq_find (fun mc -> snd mc = c) log0 in *)
     (*  Some? found /\ fst (Some.v found) = res) *)
    )
  ))

// BEGIN: EtMCPADecrypt
let decrypt k c =
  if ind_cpa_rest_adv then
    let log = !k.log in
    match seq_find (fun mc -> snd mc = c) log with
    | Some mc -> fst mc
  else
    let iv,c' = split c ivsize in
    coerce (CoreCrypto.block_decrypt AES_128_CBC k.raw iv c')
// END: EtMCPADecrypt
