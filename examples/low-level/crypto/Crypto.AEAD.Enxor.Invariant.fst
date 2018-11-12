module Crypto.AEAD.Enxor.Invariant

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
open Crypto.AEAD.Encrypt.Invariant

(*
 * enxor does not modify the aead log
 *)
private val frame_aead_entries_enxor
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (aead_st:aead_state i rw{safeMac i})
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (h0 h1:mem) : Lemma
  (requires (enxor_h0_h1 aead_st nonce aad plain ct h0 h1))
  (ensures  (HS.sel #(aead_entries i) h0 (st_ilog aead_st) ==              
             HS.sel #(aead_entries i) h1 (st_ilog aead_st)))
#reset-options "--z3rlimit 64 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let frame_aead_entries_enxor #i #rw #aadlen #plainlan aead_st nonce aad plain ct h0 h1 = ()

(*
 * enxor does not modify any existing reference in the mac region
 *)
private val frame_mac_region_enxor
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (aead_st:aead_state i rw{safeMac i})
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (h0 h1:mem) : Lemma
  (requires (enxor_h0_h1 aead_st nonce aad plain ct h0 h1))
  (ensures  (HS.modifies_ref aead_st.prf.mac_rgn Set.empty h0 h1))
let frame_mac_region_enxor #i #rw #aadlen #plainlen aead_st nonce aad plain ct h0 h1 = ()

(*
 * after enxor, unused mac exists for nonce in the prf table
 * the proof works in two steps:
     -- first, since enxor does not modify any existing reference in the mac region, we move h0 -to-> h1 (frame_unused_mac_exists_h)
     -- second, since enxor only adds otp entries, we use frame_unused_mac_exists_append to move table0 -to-> table1
 *)
private val frame_unused_mac_exists_enxor
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
  (requires (enxor_h0_h1 aead_st nonce aad plain ct h0 h1))
  (ensures  (safeMac i ==>
             (let table = HS.sel h1 (itable i aead_st.prf) in
	      let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
	      unused_mac_exists table dom_0 h1)))
#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let frame_unused_mac_exists_enxor #i #rw #aadlen #plainlen aead_st nonce aad plain ct h0 h1 =
  let cipher = cbuf ct in
  if safeMac i then begin
    let table_0 = HS.sel h0 (itable i aead_st.prf) in
    let table_1 = HS.sel h1 (itable i aead_st.prf) in
    let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
    frame_mac_region_enxor aead_st nonce aad plain ct h0 h1;  //establish that no existing reference in the mac region is modified
    frame_unused_mac_exists_h table_0 dom_0 h0 h1;  //go from h0 to h1
    let suffix = Seq.slice table_1 (Seq.length table_0) (Seq.length table_1) in
    assert (Seq.equal table_1 (Seq.append table_0 suffix));
    find_mac_all_above_1 suffix nonce;  //establish that all the entries in the suffix are above 1st domain
    frame_unused_mac_exists_append table_0 dom_0 suffix h1  //move from table0 to table1
  end

(*
 * after enxor, all the fresh nonces except nonce itself, are unused
 *)
private val intro_fresh_nonces_are_unused_except_enxor
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:nz_ok_len_32 i)
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (ct:ctagbuf plainlen)
  (h0 h1:mem) 
  : Lemma
    (requires (enxor_h0_h1 aead_st nonce aad plain ct h0 h1))
    (ensures (safeMac i ==>  (
	      let entries_1   = HS.sel #(aead_entries i) h1 (st_ilog aead_st) in
	      let table_1     = HS.sel h1 (itable i aead_st.prf) in
	      fresh_nonces_are_unused_except nonce table_1 entries_1 h1)))
#reset-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let intro_fresh_nonces_are_unused_except_enxor
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
  if safeMac i then begin
      let h1 : (h:mem{safeMac i}) = h1 in
      let entries_0   = HS.sel #(aead_entries i) h0 (st_ilog aead_st) in
      let entries_1   = HS.sel #(aead_entries i) h1 (st_ilog aead_st) in
      let table_0     = HS.sel h0 (itable i aead_st.prf) in
      let table_1     = HS.sel h1 (itable i aead_st.prf) in
      let suffix = Seq.slice table_1 (Seq.length table_0) (Seq.length table_1) in
      let x_1 = {iv = nonce; ctr=otp_offset i} in
      assert (Seq.equal table_1 (Seq.append table_0 suffix));
      assert (all_above x_1 suffix);
      assert (entries_0 == entries_1);
      assert (fresh_nonce_st nonce aead_st h1);
      assert (fresh_nonces_are_unused table_0 entries_0 h0);
      let aux (nonce':Cipher.iv (alg i)) 
	: Lemma
	  (requires (fresh_nonce nonce' entries_1 /\ nonce' <> nonce))
	  (ensures (unused_aead_iv_for_prf table_1 nonce' h1)) = 
	  assert (unused_aead_iv_for_prf table_0 nonce' h1);
	  let aux' (y:PRF.domain i{y.iv=nonce'}) 
	    : Lemma (PRF.find suffix y == None) 
	    = find_other_iv_all_above suffix x_1 y 
	  in
	  FStar.Classical.forall_intro aux';
	  frame_unused_aead_iv_for_prf_append table_0 suffix h1 nonce' 
      in	  
      FStar.Classical.(forall_intro (move_requires aux))
  end

(*
 * main lemma that propagates the invariant across enxor
 * basically, if h0 and h1 are related by enxor_h0_h1, then h1 satisfies the enxor_and_maybe_mac
 *)
val lemma_propagate_inv_enxor
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
  (requires (enxor_h0_h1 aead_st nonce aad plain ct h0 h1))
  (ensures  (enxor_and_maybe_mac false aead_st nonce aad plain ct h1))
let lemma_propagate_inv_enxor #i #rw #aadlen #plainlen aead_st nonce aad plain ct h0 h1 =
  let open FStar.Classical in
  let cipher = cbuf ct in
  if safeMac i then begin
    let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
    let entries_0   = HS.sel #(aead_entries i) h0 (st_ilog aead_st) in
    let entries_1   = HS.sel #(aead_entries i) h1 (st_ilog aead_st) in
    let table_0     = HS.sel h0 (itable i aead_st.prf) in
    let table_1     = HS.sel h1 (itable i aead_st.prf) in
    assert (entries_0 == entries_1);
    assert (fresh_nonce_st nonce aead_st h1);
    intro_fresh_nonces_are_unused_except_enxor aead_st nonce aad plain ct h0 h1;
    frame_aead_entries_enxor aead_st nonce aad plain ct h0 h1;
    frame_mac_region_enxor   aead_st nonce aad plain ct h0 h1;
    frame_unused_mac_exists_enxor aead_st nonce aad plain ct h0 h1;
    frame_refines_entries_h i aead_st.prf.mac_rgn table_0 entries_1 h0 h1;
    if safeId i then begin
      let otp_blocks = counterblocks i aead_st.prf.mac_rgn (PRF.incr i dom_0)
    		                   (v plainlen) 0 (v plainlen)
    			           (Plain.sel_plain h1 plainlen plain)
    			           (Buffer.as_seq h1 cipher) in

      frame_refines_entries_prf_append table_0 entries_1 h1 otp_blocks;
      frame_prf_contains_all_otp_blocks_prefix 
	  (PRF.incr i dom_0) 
	  (Plain.sel_plain h1 plainlen plain)
    	  (Buffer.as_seq h1 cipher) 
	  table_0
     end					     
  end
