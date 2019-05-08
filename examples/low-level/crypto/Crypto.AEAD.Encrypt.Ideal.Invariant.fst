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
module Crypto.AEAD.Encrypt.Ideal.Invariant
open FStar.UInt32
open FStar.HyperStack
open FStar.Monotonic.RRef

open Crypto.Indexing
open Flag
open Crypto.Symmetric.PRF

open Crypto.AEAD.Encoding
open Crypto.Plain
open Crypto.Symmetric.Bytes

open Crypto.AEAD.Invariant
open Crypto.AEAD.Encrypt.Invariant

module HS  = FStar.HyperStack

module MAC = Crypto.Symmetric.MAC
module PRF = Crypto.Symmetric.PRF
module CMA = Crypto.Symmetric.UF1CMA
module Cipher = Crypto.Symmetric.Cipher
module BufferUtils = Crypto.AEAD.BufferUtils

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"      
let safeMac_ideal_writes 
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (h0 h1:mem) =
  enc_dec_liveness_and_separation aead_st aad plain ct h0 /\
  (if safeMac i then
    let aead_entries_0 = HS.sel h0 (st_ilog aead_st) in
    let aead_entries_1 = HS.sel h1 (st_ilog aead_st) in
    HS.modifies (Set.singleton aead_st.log_region) h0 h1 /\
    HS.modifies_ref aead_st.log_region (Set.singleton (FStar.Heap.addr_of (HS.as_ref (aead_log_as_ref aead_st.log)))) h0 h1 /\
    aead_entries_1 
      == Seq.snoc 
                      aead_entries_0 
		      (AEADEntry nonce 
				 (Buffer.as_seq h0 aad) 
				 (v plainlen) 
				 (sel_plain h0 plainlen plain) 
				 (Buffer.as_seq h0 ct))
   else h0 == h1)

val frame_ideal_writes
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (h0 h1:mem) : Lemma
  (requires (safeMac_ideal_writes aead_st nonce aad plain ct h0 h1))
  (ensures  (enc_dec_liveness_and_separation aead_st aad plain ct h0 /\
 	     enc_dec_liveness_and_separation aead_st aad plain ct h1 /\
             (safeMac i ==> (
	       let table_0 = HS.sel h0 (itable i aead_st.prf) in
	       let table_1 = HS.sel h1 (itable i aead_st.prf) in
	       table_0 == table_1 /\
	       sel_plain h0 plainlen plain == sel_plain h1 plainlen plain /\
	       Buffer.as_seq h0 ct == Buffer.as_seq h1 ct                             /\
	       Buffer.as_seq h0 aad == Buffer.as_seq h1 aad                           /\
	       HS.modifies_ref aead_st.prf.mac_rgn Set.empty h0 h1))))
let frame_ideal_writes #i #rw #aadlen #plainlen aead_st nonce aad plain cipher_tagged h0 h1 = ()

val fresh_nonces_are_unused_after_ideal
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (h0:mem) (h1:mem{safeMac i})
  : Lemma 
      (requires (safeMac_ideal_writes aead_st nonce aad plain ct h0 h1 /\ (
		 let entries_0 = HS.sel h0 (st_ilog aead_st) in
		 let prf_table_0 = HS.sel h0 (PRF.itable i aead_st.prf) in
		 fresh_nonces_are_unused_except nonce prf_table_0 entries_0 h0)))
      (ensures  (enc_dec_liveness_and_separation aead_st aad plain ct h1 /\ (
		 let entries_1 = HS.sel h1 (st_ilog aead_st) in
		 let prf_table_1 = HS.sel h1 (PRF.itable i aead_st.prf) in
		 fresh_nonces_are_unused prf_table_1 entries_1 h1)))
let fresh_nonces_are_unused_after_ideal #i #rw #aadlen #plainlen aead_st nonce aad plain ct h0 h1 = 
    frame_ideal_writes aead_st nonce aad plain ct h0 h1;
    let entries_0 = HS.sel h0 (st_ilog aead_st) in
    let c = Buffer.as_seq h0 ct in
    let ad = Buffer.as_seq h0 aad in
    let p = sel_plain h0 plainlen plain in
    let entry = AEADEntry nonce ad (v plainlen) p c in
    let entries_1 = HS.sel h1 (st_ilog aead_st) in 
    let prf_table = HS.sel h0 (PRF.itable i aead_st.prf) in
    assert (entries_1 == Seq.snoc entries_0 entry);
    let aux (iv:Cipher.iv (alg i)) : Lemma
	(requires (fresh_nonce iv entries_1))
	(ensures (unused_aead_iv_for_prf prf_table iv h1)) =
	FStar.Seq.find_snoc entries_0 entry (is_aead_entry_nonce iv) 
    in	
    FStar.Classical.(forall_intro (move_requires aux))
		 
val reestablish_inv
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (h0 h1:mem) : Lemma
  (requires (enxor_and_maybe_mac true aead_st nonce aad plain ct h0 /\
	     safeMac_ideal_writes aead_st nonce aad plain ct h0 h1))
  (ensures (inv aead_st h1))
let reestablish_inv #i #rw #aadlen #plainlen aead_st nonce aad plain ct h0 h1 = 
  frame_ideal_writes aead_st nonce aad plain ct h0 h1;
  if safeMac i 
  then begin 
    let cipher = cbuf ct in 
    let tag = ctag ct in 
    let prf_table = HS.sel h0 (itable i aead_st.prf) in
    let t = Buffer.as_seq h0 tag in
    let c = Buffer.as_seq h0 cipher in
    let ad = Buffer.as_seq h0 aad in
    let p = sel_plain h0 plainlen plain in
    let entries_0 = HS.sel h0 (st_ilog aead_st) in
    let entry = AEADEntry nonce ad (v plainlen) p (Buffer.as_seq h0 ct) in    
    let entries_1 = Seq.snoc entries_0 entry in
    frame_refines_entries_h i aead_st.prf.mac_rgn prf_table entries_0 h0 h1;
    assert (aead_entries_are_refined prf_table entries_0 h1);
    if safeId i then begin
        let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
    	let _ = frame_mac_is_set_h prf_table nonce ad (v plainlen) c t h0 h1 in
    	let _ = assert (mac_is_set prf_table nonce ad (v plainlen) c t h1) in
    	let _ = assert (prf_contains_all_otp_blocks (PRF.incr i dom_0) 0 p c prf_table) in
        assert (refines_one_entry prf_table entry h1);
	aead_entries_are_refined_snoc prf_table entries_0 entry h1
    end;
    fresh_nonces_are_unused_after_ideal aead_st nonce aad plain ct h0 h1
  end
