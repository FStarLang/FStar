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
module Crypto.AEAD.Encrypt.Invariant

open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.Monotonic.RRef

open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Crypto.Plain
open Flag

open Crypto.AEAD.Encoding 
open Crypto.Symmetric.PRF

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module MAC    = Crypto.Symmetric.MAC
module CMA    = Crypto.Symmetric.UF1CMA
module Cipher = Crypto.Symmetric.Cipher
module PRF    = Crypto.Symmetric.PRF
module Plain  = Crypto.Plain

open Crypto.AEAD.Invariant

(*
 * a predicate on the state before calling enxor
 *)
let enxor_pre
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher:lbuffer (v plainlen))
  (h0:mem) =
  let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
  inv aead_st h0                                              /\    //the main stateful invariant holds (ensured by prf_mac)
  enc_dec_liveness_and_separation aead_st aad plain cipher h0 /\    //liveness and separation invariants
  (safeMac i ==>
    (let prf = itable i aead_st.prf in
     let table_0 = HS.sel h0 prf in
     fresh_nonce_st nonce aead_st h0  /\                            //nonce is fresh in the aead log
     unused_mac_exists table_0 dom_0 h0))                             //unused mac exists for nonce (ensured by prf_mac)

(*
 * predicate relating the states before and after calling enxor
 *)
let enxor_h0_h1
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher_tagged:ctagbuf plainlen)
  (h0 h1:mem) =
  let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
  let cipher = cbuf cipher_tagged in
  let rgns = Set.as_set [aead_st.prf.rgn; Buffer.frameOf cipher] in
  HS.(is_stack_region h0.tip) /\
  HS.(is_stack_region h1.tip) /\    //the tip of the stack is not root
  enxor_pre aead_st nonce aad plain cipher h0                 /\          //enxor_pre holds for h0
  enc_dec_liveness_and_separation aead_st aad plain cipher_tagged h1 /\   //liveness and separation ghold in h1
  (safeMac i ==>  (
     let prf = itable i aead_st.prf in
     let table_0 = HS.sel h0 prf in
     let table_1 = HS.sel h1 prf in
     HS.modifies rgns h0 h1                                                            /\    //enxor only modifies the PRF region, and the cipher buffer region
     HS.modifies_ref aead_st.prf.rgn (Set.singleton (Heap.addr_of (HS.as_ref prf))) h0 h1 /\    //in the PRF region, enxor only modifies the PRF table reference
     table_differs_only_above_x (PRF.incr i dom_0) table_0 table_1 /\                            //table_1 = table_0 ++ (otp entries)
     (safeId i ==> 
      Seq.equal table_1 (Seq.append table_0                                                    //where otp entries are exactly the ones returned by counterblocks
		                  (counterblocks i aead_st.prf.mac_rgn 
						 (PRF.incr i dom_0)
				                 (v plainlen) 0 (v plainlen)
					         (Plain.sel_plain h1 plainlen plain)
					         (Buffer.as_seq h1 cipher))))))


let fresh_nonces_are_unused_except (#i:id) (#mac_rgn:region) (nonce:Cipher.iv (alg i))
				   (prf_table:prf_table mac_rgn i) (aead_entries:aead_entries i) 
				   (h:mem{safeMac i}) = 
   forall (nonce':Cipher.iv (alg i)). (fresh_nonce nonce' aead_entries /\ nonce' <> nonce) ==>
      unused_aead_iv_for_prf prf_table nonce' h

(*
 * predicate on the final state after enxor
 *)
let enxor_and_maybe_mac
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (maybe_mac:bool)
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (h1:mem) =
  let cipher = cbuf ct in
  let tag = ctag ct in 
  HS.(is_stack_region h1.tip) /\
  enc_dec_liveness_and_separation aead_st aad plain ct h1 /\
  (safeMac i ==>
   (let aead_entries_1 = HS.sel h1 (st_ilog aead_st) in
    let table_1 = HS.sel h1 (itable i aead_st.prf) in
    let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
    fresh_nonce_st nonce aead_st h1 /\                                 //nonce is fresh in h1 (no corresponding aead entry)
    fresh_nonces_are_unused_except nonce table_1 aead_entries_1 h1 /\    //except nonce, all fresh nonces are unused
    aead_entries_are_refined table_1 aead_entries_1 h1 /\                //all aead entries are refined by the prf table
    (if maybe_mac 
     then mac_is_set table_1 nonce (Buffer.as_seq h1 aad) (v plainlen) (Buffer.as_seq h1 cipher) (Buffer.as_seq h1 tag) h1
     else unused_mac_exists table_1 dom_0 h1) /\                         //if maybe_mac is false, then unused mac exists for nonce
    (safeId i ==> prf_contains_all_otp_blocks (PRF.incr i dom_0) 0     //prf table contains all the otp entries for nonce
	                        (Plain.sel_plain h1 plainlen plain)
	                        (Buffer.as_seq h1 cipher) table_1)))

(*
 * lemma for propagating the invariant across accumulate
 * since it's a comparatively trivial lemma, adding it here (instead of a new module for accumulate invariants itself)
 *)
val lemma_propagate_inv_accumulate
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (maybe_mac:bool)
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (h0 h1:mem) : Lemma
  (requires (enxor_and_maybe_mac maybe_mac aead_st nonce aad plain ct h0 /\
	     Buffer.modifies_0 h0 h1))
  (ensures  (enxor_and_maybe_mac maybe_mac aead_st nonce aad plain ct h1))
#reset-options "--z3rlimit 512 --initial_fuel 0 --max_fuel 2 --initial_ifuel 0 --max_ifuel 2"
let lemma_propagate_inv_accumulate #i #rw #aadlen #plainlen maybe_mac aead_st nonce aad plain ct h0 h1 =
  let open FStar.Classical in
  Buffer.lemma_reveal_modifies_0 h0 h1;
  let cipher = cbuf ct in
  let tag = ctag ct in
  assert (Plain.sel_plain h0 plainlen plain == Plain.sel_plain h1 plainlen plain);
  let ad_0      = Buffer.as_seq h0 aad in
  let ad_1      = Buffer.as_seq h1 aad in
  let c0 = Buffer.as_seq h0 cipher in
  let c1 = Buffer.as_seq h1 cipher in
  let t0 = Buffer.as_seq h0 tag in
  let t1 = Buffer.as_seq h0 tag in  
  assert (c0 == c1);
  assert (ad_0 == ad_1);
  assert (t0 == t1);
  if safeMac i then begin
    let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
    let entries_0 = HS.sel #(aead_entries i) h0 (st_ilog aead_st) in
    let table_0   = HS.sel h0 (itable i aead_st.prf) in

    let entries_1 = HS.sel #(aead_entries i) h1 (st_ilog aead_st) in
    let table_1   = HS.sel h1 (itable i aead_st.prf) in    

    assert (table_0 == table_1);
    assert (entries_0 == entries_1);
    frame_refines_entries_h i aead_st.prf.mac_rgn table_0 entries_0 h0 h1;

    if maybe_mac 
    then frame_mac_is_set_h table_0 nonce ad_0 (v plainlen) c0 t0 h0 h1
    else frame_unused_mac_exists_h table_0 dom_0 h0 h1
  end

(*
 * predicate relating the initial and final state for mac_wrapper
 *)
let mac_wrapper_h0_h1
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (mac_st:CMA.state (i, nonce))
  (h0 h1:mem) =
  let cipher = cbuf ct in
  let tag = ctag ct in
  HS.(is_stack_region h0.tip) /\
  HS.(is_stack_region h1.tip) /\                                //the tip of h0 and h1 are stack regions  
  enxor_and_maybe_mac false aead_st nonce aad plain ct h0 /\    //enxor_and_maybe_mac holds for h0 (ensured by enxor)
  enc_dec_liveness_and_separation aead_st aad plain ct h1 /\    //liveness and separation hold for h1
  CMA.(mac_st.region = aead_st.prf.mac_rgn) /\                  //mac_st is in the mac region associated with the mac_rgn of aead_st.prf
  (safeMac i ==>  (
    let open HS in
    let prf_table_1 = HS.sel h1 (itable i aead_st.prf) in
    HS.modifies (Set.as_set [h0.tip; aead_st.prf.mac_rgn; Buffer.frameOf ct]) h0 h1 /\               //mac_wrapper modifies the tip of the stack, prf.mac_rgn (it sets the tag in the mac log), and the cipher text region (adds tag to the cipher text buffer)
    HS.modifies_ref aead_st.prf.mac_rgn (Set.singleton (Heap.addr_of (HS.as_ref (as_hsref (CMA.(ilog mac_st.log)))))) h0 h1  /\    //in the mac region, it only modifies the mac log associated with mac_st
    Buffer.modifies_buf_1 (Buffer.frameOf ct) tag h0 h1 /\    //mac_wrapper modifies the tag component of the ciphertext buffer
    mac_is_set prf_table_1 nonce (Buffer.as_seq h1 aad) (v plainlen) (Buffer.as_seq h1 cipher) (Buffer.as_seq h1 tag) h1))    //and finally, mac_is_set for nonce
