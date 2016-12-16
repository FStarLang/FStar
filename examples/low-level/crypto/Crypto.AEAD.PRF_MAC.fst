module Crypto.AEAD.PRF_MAC
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

module HS  = FStar.HyperStack

module MAC = Crypto.Symmetric.MAC
module PRF = Crypto.Symmetric.PRF
module CMA = Crypto.Symmetric.UF1CMA
module Cipher = Crypto.Symmetric.Cipher
module BufferUtils = Crypto.AEAD.BufferUtils

///////////////////////////////////////////////////////////////////
// AEAD functions and lemmas related to the invariant and prf_mac
//////////////////////////////////////////////////////////////////

(*
 * There are two cases for prf_mac:
 *   Either the unset mac was already there (prf_mac_existed)
 *   Or prf_mac added a new (unset) mac entry to the PRF log (prf_mac_added)
 *)

(*****)

let prf_mac_existed (i:id) (t:PRF.state i) (k_0: CMA.akey t.mac_rgn i) (x:PRF.domain_mac i)
		    (h0:mem) (returned_mac:CMA.state (i,x.iv)) 
		    (h1:mem) (existing_mac:CMA.state (i, x.iv))
  = h0 == h1 /\                                               //we didn't change the state
    returned_mac == existing_mac        /\                    //we returned the mac we found
    CMA.(MAC.norm h1 returned_mac.r)    /\                    //it's repr is in canonical form
    CMA.(Buffer.live h1 returned_mac.s) /\                    //it's live
    CMA.(mac_log ==> m_contains (ilog returned_mac.log) h1)  //and its underlying log is live too

let prf_mac_added (i:id{prf i}) (t:PRF.state i) (k_0: CMA.akey t.mac_rgn i) (x:PRF.domain_mac i)
		  (h0:mem) (returned_mac:CMA.state (i,x.iv)) (h1:mem)
  = let r = itable i t in
    let t0 = HS.sel h0 r in
    let t1 = HS.sel h1 r in
    match find_mac t1 x with 
    | Some mac_entry -> 
      returned_mac == mac_entry                              /\ //returned what is now in the table
      t1 == SeqProperties.snoc t0 (PRF.Entry x returned_mac) /\ //precisely extended the table with 1 new entry
      CMA.genPost (i,x.iv) t.mac_rgn h0 returned_mac h1      /\ //the mac is freshly generated (and unset)
      HS.modifies_transitively (Set.singleton t.rgn) h0 h1   /\ //only touched the prf's region (and its children)
      HS.modifies_ref t.rgn !{HS.as_ref r} h0 h1             /\ //in the prf region, only modified the table
      HS.modifies_ref t.mac_rgn TSet.empty h0 h1               //in the mac region, didn't touch any existing ref
    | None -> False //we definitely allocated a new mac, so we should find it

let prf_mac_ensures (i:id) (t:PRF.state i) (k_0: CMA.akey t.mac_rgn i) (x:PRF.domain_mac i)
		    (h0:mem) (returned_mac:CMA.state (i, x.iv)) (h1:mem)
  = if prf i then
      let r = itable i t in
      let t0 = HS.sel h0 r in
      let t1 = HS.sel h1 r in
      (forall (y:domain i).{:pattern (PRF.find t1 y)} y <> x ==> PRF.find t0 y == PRF.find t1 y)  /\ //at most modifies t at x
      (match find_mac t0 x with // already in the table? yes, from some (unsuccessful) decrypt call earlier
       | Some existing_mac ->
         prf_mac_existed i t k_0 x h0 returned_mac h1 existing_mac
       | None ->
         prf_mac_added i t k_0 x h0 returned_mac h1)
    else 
      CMA.genPost (i,x.iv) t.mac_rgn h0 returned_mac h1 /\
      HS.modifies_transitively (Set.singleton t.rgn) h0 h1 /\ //allocates in t.rgn
      HS.modifies_ref t.rgn TSet.empty h0 h1  /\              //but nothing within it is modified
      HS.modifies_ref t.mac_rgn TSet.empty h0 h1

(*****)

private val lemma_aead_entries_are_same_after_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw{safeMac i})
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  (h0 h1:mem)
  (mac:CMA.state (i, x.iv)) : Lemma
  (requires (h0 `HS.contains` (st_ilog aead_st) /\
             prf_mac_ensures i aead_st.prf k_0 x h0 mac h1))
  (ensures  (let entries_0 = HS.sel #(aead_entries i) h0 aead_st.log in
             let entries_1 = HS.sel #(aead_entries i) h1 aead_st.log in
	     entries_0 == entries_1))
#set-options "--z3rlimit 100"
let lemma_aead_entries_are_same_after_prf_mac #i #rw aead_st k_0 x h0 h1 mac = ()

#reset-options
private val frame_fresh_nonce_st_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw{safeMac i})
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  (h0 h1:mem)
  (mac:CMA.state (i, x.iv))
  (iv:Cipher.iv (alg i)) : Lemma
  (requires (h0 `HS.contains` (st_ilog aead_st) /\
             prf_mac_ensures i aead_st.prf k_0 x h0 mac h1))
  (ensures  (fresh_nonce_st iv aead_st h0 <==> fresh_nonce_st iv aead_st h1))
let frame_fresh_nonce_st_prf_mac #i #rw aead_st k_0 x h0 h1 mac iv =
  lemma_aead_entries_are_same_after_prf_mac aead_st k_0 x h0 h1 mac

private val lemma_unused_mac_exists_after_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw)
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  (mac:CMA.state (i,x.iv))
  (h0 h1:mem) : Lemma
  (requires inv aead_st h0 /\
            (safeMac i ==> fresh_nonce_st x.iv aead_st h0) /\
            prf_mac_ensures i aead_st.prf k_0 x h0 mac h1)
  (ensures (safeMac i ==>
            (let table = HS.sel h1 (itable i aead_st.prf) in
	     unused_mac_exists table x h1)))
let lemma_unused_mac_exists_after_prf_mac #i #rw aead_st k_0 x mac h0 h1 = ()

(*
 * The proof case analyzes on PRF.find_mac table_0 x
 *   -- If it's Some, we know that the PRF table and the heap did not change, and we are done
 *   -- If it's None, we go in two steps:
 *      -- First we show that aead entries are still refined with table_0 and h1, since the mac region did not change from h0 -to-> h1
 *         (frame_refines_entries_h)
 *      -- Then we precisely know that table_1 is append of a single block to table_0, we show that entries are still refined
 *         (frame_refines_entries_prf_append)
 *)
private val frame_refines_aead_entries_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw{safeMac i})
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  (h0 h1:mem)
  (mac:CMA.state (i, x.iv)) : Lemma
  (requires (h0 `HS.contains` (st_ilog aead_st) /\
             (let entries_0 = HS.sel #(aead_entries i) h0 aead_st.log in
	      let table_0 = HS.sel h0 (itable i aead_st.prf) in
              aead_entries_are_refined table_0 entries_0 h0 /\
	      prf_mac_ensures i aead_st.prf k_0 x h0 mac h1)))
  (ensures  (let entries_1 = HS.sel #(aead_entries i) h1 aead_st.log in
	     let table_1 = HS.sel h1 (itable i aead_st.prf) in
             aead_entries_are_refined table_1 entries_1 h1))
let frame_refines_aead_entries_prf_mac #i #rw aead_st k_0 x h0 h1 mac =
  let aead_ent_0 = HS.sel #(aead_entries i) h0 aead_st.log in
  //this is recalling that aead_entries are not changed from h0 to h1, makes the proof go faster
  lemma_aead_entries_are_same_after_prf_mac aead_st k_0 x h0 h1 mac;
  
  let table_0 = HS.sel h0 (itable i aead_st.prf) in
  match PRF.find_mac table_0 x with
  | Some _ -> ()
  | None   ->
    frame_refines_entries_h i aead_st.prf.mac_rgn table_0 aead_ent_0 h0 h1;
    frame_refines_entries_prf_append table_0 aead_ent_0 h1 (Seq.create 1 (PRF.Entry x mac))

private val lemma_iv_of_x_is_unused_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw{safeMac i})
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  (mac:CMA.state (i, x.iv))
  (h0 h1:mem) : Lemma
  (requires (let table_0 = HS.sel h0 (itable i aead_st.prf) in
             unused_aead_iv_for_prf table_0 x.iv h0 /\
             prf_mac_ensures i aead_st.prf k_0 x h0 mac h1))
  (ensures  (let table_1 = HS.sel h1 (itable i aead_st.prf) in
             unused_aead_iv_for_prf table_1 x.iv h1))
let lemma_iv_of_x_is_unused_prf_mac #i #rw aead_st k_0 x mac h0 h1 = ()

(*
 * Factoring it out, makes the proof go faster
 *)
val frame_cma_mac_is_unset_h
  (i:CMA.id)
  (r:rid{is_eternal_region r})
  (r':rid{r' `HS.is_above` r})
  (mac_st:CMA.state i)
  (h0 h1:mem) : Lemma
  (requires (CMA.mac_is_unset i r mac_st h0 /\
             HS.modifies_transitively (Set.singleton r') h0 h1 /\
             HS.modifies_ref r TSet.empty h0 h1))
  (ensures  (CMA.mac_is_unset i r mac_st h1))
let frame_cma_mac_is_unset_h i r r' mac_st h0 h1 = ()

private val frame_unused_aead_iv_different_from_x_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw{safeMac i})
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  (mac:CMA.state (i, x.iv))
  (h0 h1:mem)
  (iv:Cipher.iv (alg i)) : Lemma
  (requires (let table_0 = HS.sel h0 (itable i aead_st.prf) in
             unused_aead_iv_for_prf table_0 iv h0 /\
             prf_mac_ensures i aead_st.prf k_0 x h0 mac h1 /\
	     not (iv = x.iv)))
  (ensures  (let table_1 = HS.sel h1 (itable i aead_st.prf) in
             unused_aead_iv_for_prf table_1 iv h1))
let frame_unused_aead_iv_different_from_x_prf_mac #i #rw aead_st k_0 x mac h0 h1 iv =
  let table_0 = HS.sel h0 (itable i aead_st.prf) in
  let table_1 = HS.sel h1 (itable i aead_st.prf) in
  let dom_0 = {iv=iv; ctr=PRF.ctr_0 i} in
  match PRF.find_mac table_1 dom_0 with
  | None           -> ()
  | Some mac_range ->
    (match PRF.find_mac table_0 x with
     | Some _ -> ()
     | None   ->
       frame_cma_mac_is_unset_h (i, iv) CMA.(mac_range.region) aead_st.prf.rgn mac_range h0 h1)

private val frame_unused_aead_iv_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw{safeMac i})
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  (mac:CMA.state (i, x.iv))
  (h0 h1:mem)
  (iv:Cipher.iv (alg i)) : Lemma
  (requires (inv aead_st h0 /\
	     fresh_nonce_st iv aead_st h0 /\
	     prf_mac_ensures i aead_st.prf k_0 x h0 mac h1))
  (ensures  (let table_1 = HS.sel h1 (itable i aead_st.prf) in
	     unused_aead_iv_for_prf table_1 iv h1))
let frame_unused_aead_iv_prf_mac #i #rw aead_st k_0 x mac h0 h1 iv =
  if iv = x.iv then lemma_iv_of_x_is_unused_prf_mac #i #rw aead_st k_0 x mac h0 h1
  else              frame_unused_aead_iv_different_from_x_prf_mac #i #rw aead_st k_0 x mac h0 h1 iv

private val frame_fresh_nonces_are_unused_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw{safeMac i})
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  (h0 h1:mem)
  (mac:CMA.state (i, x.iv)) : Lemma
  (requires (inv aead_st h0 /\
             prf_mac_ensures i aead_st.prf k_0 x h0 mac h1))
  (ensures  (let entries_1 = HS.sel #(aead_entries i) h1 aead_st.log in
	     let table_1 = HS.sel h1 (itable i aead_st.prf) in
             fresh_nonces_are_unused table_1 entries_1 h1))
let frame_fresh_nonces_are_unused_prf_mac #i #rw aead_st k_0 x h0 h1 mac =
  let open FStar.Classical in
  forall_intro (move_requires (frame_fresh_nonce_st_prf_mac aead_st k_0 x h0 h1 mac));
  forall_intro (move_requires (frame_unused_aead_iv_prf_mac aead_st k_0 x mac h0 h1))

private val frame_inv_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw)
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  (h0 h1:mem)
  (mac:CMA.state (i, x.iv)) : Lemma
  (requires (inv aead_st h0 /\
             prf_mac_ensures i aead_st.prf k_0 x h0 mac h1))
  (ensures  (inv aead_st h1))
let frame_inv_prf_mac #i #rw aead_st k_0 x h0 h1 mac =
  if safeMac i then begin
    frame_refines_aead_entries_prf_mac aead_st k_0 x h0 h1 mac;
    frame_fresh_nonces_are_unused_prf_mac aead_st k_0 x h0 h1 mac
  end

val prf_mac_wrapper
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw)
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  : ST (CMA.state (i,x.iv))
       (requires (fun h0 -> inv aead_st h0 /\
                         (safeMac i ==> fresh_nonce_st x.iv aead_st h0)))
       (ensures (fun h0 mac h1 -> prf_mac_ensures i aead_st.prf k_0 x h0 mac h1 /\
			       inv aead_st h1 /\
                               (safeMac i ==>
			         (let table_1 = HS.sel h1 (itable i aead_st.prf) in
				  fresh_nonce_st x.iv aead_st h1 /\
				  unused_mac_exists table_1 x h1 /\
				  none_above (PRF.incr i x) table_1)))) //adding this none_above clause to match the precondition of the next step in the encrypt function, it's easily provable from inv h1 and fresh_nonce x.iv h1
let prf_mac_wrapper #i #rw aead_st k_0 x =
  let h0 = get () in
  
  let mac = PRF.prf_mac i aead_st.prf k_0 x in

  let h1 = get () in
  lemma_unused_mac_exists_after_prf_mac aead_st k_0 x mac h0 h1;
  frame_inv_prf_mac aead_st k_0 x h0 h1 mac;
  let _ =
    if safeMac i then frame_fresh_nonce_st_prf_mac aead_st k_0 x h0 h1 mac x.iv
    else ()
  in
  mac

let ak_live (#i:CMA.id) (r:rid) (ak:CMA.state i) (h:mem) = 
    let open CMA in 
    ak.region = r /\
    Buffer.live h ak.s /\
    MAC.norm h ak.r

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
val prf_mac_enc
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw)
  (#aadlen:aadlen) (aad:lbuffer (v aadlen))
  (#len:txtlen_32) (plain:plainBuffer i (v len)) (cipher_tagged:lbuffer (v len + v MAC.taglen))
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  : ST (CMA.state (i,x.iv))
       (requires (fun h0 -> 
		   enc_dec_separation aead_st aad plain cipher_tagged /\
		   enc_dec_liveness aead_st aad plain cipher_tagged h0 /\
		   inv aead_st h0 /\
                   (safeMac i ==> fresh_nonce_st x.iv aead_st h0)))
       (ensures (fun h0 ak h1 -> 
       		   enc_dec_liveness aead_st aad plain cipher_tagged h1 /\
		   prf_mac_ensures i aead_st.prf k_0 x h0 ak h1 /\
		   BufferUtils.prf_mac_modifies aead_st.log_region aead_st.prf.mac_rgn h0 h1 /\
   		   ak_live PRF.(aead_st.prf.mac_rgn) ak h1 /\
		   inv aead_st h1 /\
                   (safeMac i ==>
		    (let table_1 = HS.sel h1 (itable i aead_st.prf) in
		     fresh_nonce_st x.iv aead_st h1 /\
		     is_mac_for_iv aead_st ak h1 /\
		     unused_mac_exists table_1 x h1 /\
		     none_above (PRF.incr i x) table_1))))
let prf_mac_enc #i #rw aead_st #aadlen aad #len plain cipher_tagged k_0 x = 
 let h0 = get () in
 let ak = prf_mac_wrapper aead_st k_0 x in
 let h1 = get () in 
 BufferUtils.intro_prf_mac_modifies aead_st.log_region aead_st.prf.mac_rgn h0 h1;
 ak

val prf_mac_dec
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw)
  (#aadlen:aadlen) (aad:lbuffer (v aadlen))
  (#len:txtlen_32) (plain:plainBuffer i (v len)) (cipher_tagged:lbuffer (v len + v MAC.taglen))
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  : ST (CMA.state (i,x.iv))
       (requires (fun h0 -> 
		   enc_dec_separation aead_st aad plain cipher_tagged /\
		   enc_dec_liveness aead_st aad plain cipher_tagged h0 /\
		   inv aead_st h0))
       (ensures (fun h0 ak h1 -> 
       		   enc_dec_liveness aead_st aad plain cipher_tagged h1 /\
		   prf_mac_ensures i aead_st.prf k_0 x h0 ak h1 /\
		   BufferUtils.prf_mac_modifies aead_st.log_region aead_st.prf.mac_rgn h0 h1 /\
		   ak_live PRF.(aead_st.prf.mac_rgn) ak h1 /\
		   inv aead_st h1))
let prf_mac_dec #i #rw aead_st #aadlen aad #len plain cipher_tagged k_0 x =
  let h0 = get () in
  let mac = PRF.prf_mac i aead_st.prf k_0 x in
  let h1 = get () in
  frame_inv_prf_mac aead_st k_0 x h0 h1 mac;
  BufferUtils.intro_prf_mac_modifies aead_st.log_region aead_st.prf.mac_rgn h0 h1;
  mac

#reset-options
let post_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (h:mem) =
  let x = {iv=nonce; ctr=PRF.ctr_0 i} in
  inv aead_st h                        /\             //invariant holds
  (safeMac i ==>
    (let table = HS.sel h (itable i aead_st.prf) in
     fresh_nonce_st nonce aead_st h    /\             //nonce remains fresh (i.e. it is not in the aead_entries in h)
     unused_mac_exists table x h /\                   //unused mac exists for the nonce
     none_above (PRF.incr i x) table))               //no OTP entries exist for the nonce in the PRF table

module Plain = Crypto.Plain

let enc_dec_liveness_and_separation (#i:id) (#rw:rw) (aead_st:aead_state i rw)
                                    (#aadlen:nat) (aad:lbuffer aadlen)
				    (#plainlen:nat) (plain: plainBuffer i plainlen)
				    (#cipherlen:nat) (cipher:lbuffer cipherlen)
                                    (h:mem)
  = enc_dec_liveness aead_st aad plain cipher h /\
    enc_dec_separation aead_st aad plain cipher

let enxor_h0_h1
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher:lbuffer (v plainlen))
  (h0 h1:mem) =
  let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
  inv aead_st h0                                              /\
  enc_dec_liveness_and_separation aead_st aad plain cipher h0 /\
  enc_dec_liveness_and_separation aead_st aad plain cipher h1 /\
  (safeId i ==>
    (let rgns = Set.as_set [aead_st.prf.rgn; Buffer.frameOf cipher] in
     let prf = itable i aead_st.prf in
     let table_0 = HS.sel h0 prf in
     let table_1 = HS.sel h1 prf in
     fresh_nonce_st nonce aead_st h0       /\
     unused_mac_exists table_0 dom_0 h0       /\
     HS.modifies rgns h0 h1                                                            /\
     HS.modifies_ref aead_st.prf.rgn (TSet.singleton (Heap.Ref (HS.as_ref prf))) h0 h1 /\
     Seq.equal table_1 (Seq.append table_0
		                  (counterblocks i aead_st.prf.mac_rgn (PRF.incr i dom_0)
				                 (v plainlen) 0 (v plainlen)
					         (Plain.sel_plain h1 plainlen plain)
					         (Buffer.as_seq h1 cipher)))))

val frame_aead_entries_enxor
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw{safeId i})
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher:lbuffer (v plainlen))
  (h0 h1:mem) : Lemma
  (requires (enxor_h0_h1 aead_st nonce aad plain cipher h0 h1))
  (ensures  (HS.sel #(aead_entries i) h0 (st_ilog aead_st) ==              
             HS.sel #(aead_entries i) h1 (st_ilog aead_st)))
#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let frame_aead_entries_enxor #i #rw #aadlen #plainlan aead_st nonce aad plain cipher h0 h1 = ()
#reset-options

(*
 * AR: this is also of the above category.
 *)
val frame_mac_region_enxor
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw{safeId i})
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher:lbuffer (v plainlen))
  (h0 h1:mem) : Lemma
  (requires (enxor_h0_h1 aead_st nonce aad plain cipher h0 h1))
  (ensures  (HS.modifies_ref aead_st.prf.mac_rgn TSet.empty h0 h1))
#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let frame_mac_region_enxor #i #rw #aadlen #plainlen aead_st nonce aad plain cipher h0 h1 = ()
#reset-options

val frame_unused_mac_exists_enxor
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher:lbuffer (v plainlen))
  (h0 h1:mem) : Lemma
  (requires (enxor_h0_h1 aead_st nonce aad plain cipher h0 h1))
  (ensures  (safeId i ==>
             (let table = HS.sel h1 (itable i aead_st.prf) in
	      let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
	      unused_mac_exists table dom_0 h1)))
let frame_unused_mac_exists_enxor #i #rw #aadlen #plainlen aead_st nonce aad plain cipher h0 h1 =
  if safeId i then begin
    let table_0 = HS.sel h0 (itable i aead_st.prf) in
    let table_1 = HS.sel h1 (itable i aead_st.prf) in
    let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
    let otp_entries = counterblocks i aead_st.prf.mac_rgn (PRF.incr i dom_0) (v plainlen) 0
                                    (v plainlen) (Plain.sel_plain h1 plainlen plain)
    			            (Buffer.as_seq h1 cipher) in
    frame_mac_region_enxor aead_st nonce aad plain cipher h0 h1;
    frame_unused_mac_exists_h table_0 dom_0 h0 h1;
    lemma_counterblocks_find_domain_mac_is_none i aead_st.prf.mac_rgn (PRF.incr i dom_0) (v plainlen) 0
                                                (v plainlen) (Plain.sel_plain h1 plainlen plain)
    					        (Buffer.as_seq h1 cipher);
    frame_unused_mac_exists_append table_0 dom_0 otp_entries h1
  end
  
val lemma_propagate_inv_enxor
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher:lbuffer (v plainlen))
  (h0 h1:mem) : Lemma
  (requires (enxor_h0_h1 aead_st nonce aad plain cipher h0 h1))
  (ensures  (enc_dec_liveness_and_separation aead_st aad plain cipher h1 /\
             (safeId i ==>
               (let aead_entries_1 = HS.sel #(aead_entries i) h1 (st_ilog aead_st) in
	        let table_1 = HS.sel h1 (itable i aead_st.prf) in
	        let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
	        fresh_nonce_st nonce aead_st h1 /\
	        aead_entries_are_refined table_1 aead_entries_1 h1 /\
	        (forall (nonce':Cipher.iv (alg i)). (fresh_nonce nonce' aead_entries_1 /\ nonce' <> nonce) ==>
	                                       unused_aead_iv_for_prf table_1 nonce' h1) /\
	        unused_mac_exists table_1 dom_0 h1 /\
	        prf_contains_all_otp_blocks (PRF.incr i dom_0) 0
	                                    (Plain.sel_plain h1 plainlen plain)
	                                    (Buffer.as_seq h1 cipher) table_1))))
let lemma_propagate_inv_enxor #i #rw #aadlen #plainlen aead_st nonce aad plain cipher h0 h1 =
  let open FStar.Classical in
  if safeId i then begin
    let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
    let entries_0   = HS.sel #(aead_entries i) h0 (st_ilog aead_st) in
    let entries_1   = HS.sel #(aead_entries i) h1 (st_ilog aead_st) in
    let table_0     = HS.sel h0 (itable i aead_st.prf) in
    let table_1     = HS.sel h1 (itable i aead_st.prf) in
    let otp_blocks = counterblocks i aead_st.prf.mac_rgn (PRF.incr i dom_0)
    		                   (v plainlen) 0 (v plainlen)
    			           (Plain.sel_plain h1 plainlen plain)
    			           (Buffer.as_seq h1 cipher) in

    frame_aead_entries_enxor aead_st nonce aad plain cipher h0 h1;
    frame_mac_region_enxor   aead_st nonce aad plain cipher h0 h1;

    frame_refines_entries_h i aead_st.prf.mac_rgn table_0 entries_1 h0 h1;
    frame_refines_entries_prf_append table_0 entries_1 h1 otp_blocks;

    let h0':(m:mem{safeMac i}) = h0 in
    forall_intro (move_requires (frame_unused_aead_iv_for_prf_h h0' h1 table_0));

    lemma_counterblocks_find_other_iv_is_none i aead_st.prf.mac_rgn (PRF.incr i dom_0) (v plainlen) 0 (v plainlen)
                                                                    (Plain.sel_plain h1 plainlen plain)
								    (Buffer.as_seq h1 cipher);
    forall_intro (move_requires (frame_unused_aead_iv_for_prf_append table_0 otp_blocks h1));

    frame_unused_mac_exists_enxor aead_st nonce aad plain cipher h0 h1;

    frame_prf_contains_all_otp_blocks_prefix (PRF.incr i dom_0) 0ul (Plain.sel_plain h1 plainlen plain)
    	                                     (Buffer.as_seq h1 cipher) table_0
  end

let accumulate_h0_h1
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher:lbuffer (v plainlen))
  (h0 h1:mem) =
  enc_dec_liveness_and_separation aead_st aad plain cipher h0 /\
  enc_dec_liveness_and_separation aead_st aad plain cipher h1 /\
  Buffer.modifies_0 h0 h1 /\
  (safeId i ==>
    (let aead_entries_0 = HS.sel #(aead_entries i) h0 (st_ilog aead_st) in
     let table_0 = HS.sel h0 (itable i aead_st.prf) in
     let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
     fresh_nonce_st nonce aead_st h0 /\
     aead_entries_are_refined table_0 aead_entries_0 h0 /\
     (forall (nonce':Cipher.iv (alg i)). (fresh_nonce nonce' aead_entries_0 /\ nonce' <> nonce) ==>
	                             unused_aead_iv_for_prf table_0 nonce' h0) /\
     unused_mac_exists table_0 dom_0 h0 /\
     prf_contains_all_otp_blocks (PRF.incr i dom_0) 0
	                         (Plain.sel_plain h0 plainlen plain)
	                         (Buffer.as_seq h0 cipher) table_0))

val lemma_propagate_inv_accumulate
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher:lbuffer (v plainlen))
  (h0 h1:mem) : Lemma
  (requires (accumulate_h0_h1 aead_st nonce aad plain cipher h0 h1))
  (ensures  (enc_dec_liveness_and_separation aead_st aad plain cipher h1 /\
             (safeId i ==>
               (let aead_entries_1 = HS.sel #(aead_entries i) h1 (st_ilog aead_st) in
	        let table_1 = HS.sel h1 (itable i aead_st.prf) in
	        let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
	        fresh_nonce_st nonce aead_st h1 /\
	        aead_entries_are_refined table_1 aead_entries_1 h1 /\
	        (forall (nonce':Cipher.iv (alg i)). (fresh_nonce nonce' aead_entries_1 /\ nonce' <> nonce) ==>
	                                       unused_aead_iv_for_prf table_1 nonce' h1) /\
	        unused_mac_exists table_1 dom_0 h1 /\
	        prf_contains_all_otp_blocks (PRF.incr i dom_0) 0
	                                    (Plain.sel_plain h1 plainlen plain)
	                                    (Buffer.as_seq h1 cipher) table_1))))
let lemma_propagate_inv_accumulate #i #rw #aadlen #plainlen aead_st nonce aad plain cipher h0 h1 =
  let open FStar.Classical in
  if safeId i then begin
    let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
    let entries_0   = HS.sel #(aead_entries i) h0 (st_ilog aead_st) in
    let table_0     = HS.sel h0 (itable i aead_st.prf) in

    Buffer.lemma_reveal_modifies_0 h0 h1;

    frame_refines_entries_h i aead_st.prf.mac_rgn table_0 entries_0 h0 h1;

    let h0':(m:mem{safeMac i}) = h0 in
    forall_intro (move_requires (frame_unused_aead_iv_for_prf_h h0' h1 table_0));

    frame_unused_mac_exists_h table_0 dom_0 h0 h1
  end

val lemma_mac_log_framing
  (#i:id)
  (nonce_1:Cipher.iv (alg i){safeId i})
  (mac_st_1:CMA.state (i, nonce_1))
  (h0 h1:mem)
  (nonce_2:Cipher.iv (alg i))
  (mac_st_2:CMA.state (i, nonce_2){CMA.(mac_st_2.region) = CMA.(mac_st_1.region)}) : Lemma
  (requires (nonce_1 <> nonce_2                                       /\
             m_contains (CMA.(ilog mac_st_2.log)) h0                /\
	     HS.modifies (Set.as_set [CMA.(mac_st_1.region)]) h0 h1 /\
             HS.modifies_ref (CMA.(mac_st_1.region)) !{HS.as_ref (as_hsref (CMA.(ilog mac_st_1.log)))} h0 h1))
  (ensures  (m_sel h0 (CMA.(ilog mac_st_2.log)) = m_sel h1 (CMA.(ilog mac_st_2.log))))
let lemma_mac_log_framing #i nonce_1 mac_st_1 h0 h1 nonce_2 mac_st_2 = ()

let lemma_find_l_exists_index
  (#a:Type)
  (s:Seq.seq a)
  (f:(a -> Tot bool)) : Lemma
  (None? (SeqProperties.find_l f s) ==> (forall (i:nat{i < Seq.length s}). not (f (Seq.index s i))))
  = admit ()

let lemma_fresh_nonce_implies_all_entries_nonces_are_different
  (#i:id)
  (aead_entries:aead_entries i)
  (nonce:Cipher.iv (alg i)) : Lemma
  (requires (fresh_nonce nonce aead_entries))
  (ensures  (forall (e:aead_entry i).{:pattern (aead_entries `SeqProperties.contains` e)}
	        aead_entries `SeqProperties.contains` e ==> e.nonce <> nonce))
  = let open FStar.Classical in
    lemma_find_l_exists_index aead_entries (is_aead_entry_nonce nonce);
    forall_intro (SeqProperties.contains_elim aead_entries)

let mac_wrapper_h0_h1
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
  (mac_st:CMA.state (i, nonce))
  (h0 h1:mem) =
  let cipher, tag = Buffer.split cipher_tagged plainlen in
  enc_dec_liveness_and_separation #i #rw aead_st #(v aadlen) aad #(v plainlen) plain #(v plainlen) cipher h0 /\
  enc_dec_liveness_and_separation #i #rw aead_st #(v aadlen) aad #(v plainlen) plain #(v plainlen) cipher h1 /\
  (safeId i ==>
    HS.modifies (Set.as_set [aead_st.prf.mac_rgn; Buffer.frameOf cipher_tagged]) h0 h1        /\
    HS.modifies_ref aead_st.prf.mac_rgn !{HS.as_ref (as_hsref (CMA.(ilog mac_st.log)))} h0 h1 /\
    Buffer.as_seq h0 cipher == Buffer.as_seq h1 cipher                                        /\
    (let aead_entries_0 = HS.sel #(aead_entries i) h0 aead_st.log in
     let table_0 = HS.sel h0 (itable i aead_st.prf) in
     let table_1 = HS.sel h1 (itable i aead_st.prf) in
     let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
     aead_entries_are_refined table_0 aead_entries_0 h0 /\
     fresh_nonce_st nonce aead_st h0 /\
     (forall (nonce':Cipher.iv (alg i)). (fresh_nonce nonce' aead_entries_0 /\ nonce' <> nonce) ==>
	                            unused_aead_iv_for_prf table_0 nonce' h0) /\
     //AR: currently i am assuming this, might need some proving
     mac_is_set table_1 nonce (Buffer.as_seq h1 aad) (v plainlen) (Buffer.as_seq h1 cipher) (Buffer.as_seq h1 tag) h1 /\
     prf_contains_all_otp_blocks (PRF.incr i dom_0) 0
	                         (Plain.sel_plain h0 plainlen plain)
	                         (Buffer.as_seq h0 cipher) table_0))

val frame_aead_entries_are_refined_mac_wrapper
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
  (mac_st:CMA.state (i, nonce))
  (h0 h1:mem) : Lemma
  (requires (mac_wrapper_h0_h1 aead_st nonce aad plain cipher_tagged mac_st h0 h1))
  (ensures  (safeId i ==>
             (let entries_0 = HS.sel #(aead_entries i) h0 (st_ilog aead_st) in
	      let table_0 = HS.sel h0 (itable i aead_st.prf) in
	      aead_entries_are_refined table_0 entries_0 h1)))
#reset-options "--z3rlimit 100"
let frame_aead_entries_are_refined_mac_wrapper #i #rw #aadlen #plainlen aead_st nonce aad plain cipher_tagged mac_st h0 h1 =
  if safeId i then begin
    let entries_0 = HS.sel #(aead_entries i) h0 (st_ilog aead_st) in
    lemma_fresh_nonce_implies_all_entries_nonces_are_different entries_0 nonce
  end (* This proof takes a long time, should debug. *)
#reset-options

val frame_unused_aead_id_for_prf_mac_wrapper
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw{safeId i})
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
  (mac_st:CMA.state (i, nonce))
  (h0 h1:mem)
  (nonce':Cipher.iv (alg i)) : Lemma
  (requires (let table_0 = HS.sel h0 (itable i aead_st.prf) in
             mac_wrapper_h0_h1 aead_st nonce aad plain cipher_tagged mac_st h0 h1 /\
             unused_aead_iv_for_prf table_0 nonce' h0 /\
	     nonce <> nonce'))
  (ensures  (let table_0 = HS.sel h0 (itable i aead_st.prf) in
             unused_aead_iv_for_prf table_0 nonce' h1))
#reset-options "--z3rlimit 100"
let frame_unused_aead_id_for_prf_mac_wrapper #i #rw #aadlen #plainlen aead_st nonce aad plain cipher_tagged mac_st h0 h1 nonce' = ()
#reset-options (* This proof also takes a long time. *)

val frame_unused_aead_id_for_prf_mac_wrapper_forall
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw{safeId i})
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
  (mac_st:CMA.state (i, nonce))
  (h0 h1:mem) : Lemma
  (requires (mac_wrapper_h0_h1 aead_st nonce aad plain cipher_tagged mac_st h0 h1))
  (ensures  (let table_0 = HS.sel h0 (itable i aead_st.prf) in
             forall (nonce':Cipher.iv (alg i)). (nonce' <> nonce /\ unused_aead_iv_for_prf table_0 nonce' h0) ==>
	                                   unused_aead_iv_for_prf table_0 nonce' h1))
let frame_unused_aead_id_for_prf_mac_wrapper_forall #i #rw #aadlen #plainlen aead_st nonce aad plain cipher_tagged mac_st h0 h1 =
  let open FStar.Classical in
  forall_intro (move_requires (frame_unused_aead_id_for_prf_mac_wrapper aead_st nonce aad plain cipher_tagged mac_st h0 h1))

val frame_entries_and_table_mac_wrapper
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
  (mac_st:CMA.state (i, nonce))
  (h0 h1:mem) : Lemma
  (requires (mac_wrapper_h0_h1 aead_st nonce aad plain cipher_tagged mac_st h0 h1))
  (ensures  (safeId i ==>
             (let entries_0 = HS.sel #(aead_entries i) h0 (st_ilog aead_st) in
              let entries_1 = HS.sel #(aead_entries i) h1 (st_ilog aead_st) in
	      let table_0 = HS.sel h0 (itable i aead_st.prf) in
	      let table_1 = HS.sel h1 (itable i aead_st.prf) in
	      entries_0 == entries_1 /\ table_0 == table_1)))
#reset-options "--z3rlimit 100"
let frame_entries_and_table_mac_wrapper #i #rw #aadlen #plainlen aead_st nonce aad plain cipher_tagged mac_st h0 h1 = ()
#reset-options (* This proof also takes a long time. *)

val lemma_propagate_inv_mac_wrapper
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
  (mac_st:CMA.state (i, nonce))
  (h0 h1:mem) : Lemma
  (requires (mac_wrapper_h0_h1 aead_st nonce aad plain cipher_tagged mac_st h0 h1))
  (ensures  (let cipher, tag = Buffer.split cipher_tagged plainlen in
             enc_dec_liveness_and_separation #i #rw aead_st #(v aadlen) aad
                                             #(v plainlen) plain #(v plainlen) cipher h1 /\
             (safeId i ==>
	       (let aead_entries_1 = HS.sel #(aead_entries i) h1 aead_st.log in
	        let table_1 = HS.sel h1 (itable i aead_st.prf) in
	        let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
	        let cipher, tag = Buffer.split cipher_tagged plainlen in
	        aead_entries_are_refined table_1 aead_entries_1 h1 /\
	        fresh_nonce_st nonce aead_st h1 /\
	        (forall (nonce':Cipher.iv (alg i)). (fresh_nonce nonce' aead_entries_1 /\ nonce' <> nonce) ==>
	                                        unused_aead_iv_for_prf table_1 nonce' h1) /\
	        mac_is_set table_1 nonce (Buffer.as_seq h1 aad) (v plainlen) (Buffer.as_seq h1 cipher) (Buffer.as_seq h1 tag) h1 /\
	        prf_contains_all_otp_blocks (PRF.incr i dom_0) 0
	                                    (Plain.sel_plain h1 plainlen plain)
	                                    (Buffer.as_seq h1 cipher) table_1))))
let lemma_propagate_inv_mac_wrapper #i #rw #aadlen #plainlen aead_st nonce aad plain cipher_tagged mac_st h0 h1 =
  if safeId i then begin
    let open FStar.Classical in
    frame_entries_and_table_mac_wrapper             aead_st nonce aad plain cipher_tagged mac_st h0 h1;
    frame_aead_entries_are_refined_mac_wrapper      aead_st nonce aad plain cipher_tagged mac_st h0 h1;
    frame_unused_aead_id_for_prf_mac_wrapper_forall aead_st nonce aad plain cipher_tagged mac_st h0 h1;

    (* AR: we should get this from separation of plain from cipher and mac region. *)
    assume (Plain.sel_plain h0 plainlen plain == Plain.sel_plain h1 plainlen plain)
  end

let final_h0_h1
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
  (h0 h1:mem) =
  let cipher, tag = Buffer.split cipher_tagged plainlen in
  enc_dec_liveness_and_separation #i #rw aead_st #(v aadlen) aad #(v plainlen) plain #(v plainlen) cipher h0 /\
  enc_dec_liveness_and_separation #i #rw aead_st #(v aadlen) aad #(v plainlen) plain #(v plainlen) cipher h1 /\
  (safeId i ==>
    HS.modifies (Set.singleton aead_st.log_region) h0 h1 /\
    HS.modifies_ref aead_st.log_region (TSet.singleton (FStar.Heap.Ref (HS.as_ref (aead_log_as_ref aead_st.log)))) h0 h1 /\
    (let aead_entries_0 = HS.sel #(aead_entries i) h0 aead_st.log in
     let aead_entries_1 = HS.sel #(aead_entries i) h1 aead_st.log in
     let table_0 = HS.sel h0 (itable i aead_st.prf) in
     let table_1 = HS.sel h1 (itable i aead_st.prf) in
     let dom_0 = {iv=nonce; ctr=PRF.ctr_0 i} in
     aead_entries_are_refined table_0 aead_entries_0 h0 /\
     fresh_nonce_st nonce aead_st h0 /\
     (forall (nonce':Cipher.iv (alg i)). (fresh_nonce nonce' aead_entries_0 /\ nonce' <> nonce) ==>
	                            unused_aead_iv_for_prf table_0 nonce' h0) /\
     mac_is_set table_0 nonce (Buffer.as_seq h0 aad) (v plainlen) (Buffer.as_seq h0 cipher) (Buffer.as_seq h0 tag) h0 /\
     prf_contains_all_otp_blocks (PRF.incr i dom_0) 0
	                         (Plain.sel_plain h0 plainlen plain)
	                         (Buffer.as_seq h0 cipher) table_0 /\
     aead_entries_1 == SeqProperties.snoc aead_entries_0 (AEADEntry nonce (Buffer.as_seq h0 aad) (v plainlen) (Plain.sel_plain h0 plainlen plain) (Buffer.as_seq h0 cipher_tagged))))

val lemma_establish_final_inv
  (#i:id)
  (#rw:rw)
  (#aadlen:aadlen_32)
  (#plainlen:txtlen_32{plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)})
  (aead_st:aead_state i rw)
  (nonce:Cipher.iv (alg i))
  (aad:lbuffer (v aadlen))
  (plain:plainBuffer i (v plainlen))
  (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
  (h0 h1:mem) : Lemma
  (requires (final_h0_h1 aead_st nonce aad plain cipher_tagged h0 h1))
  (ensures (inv aead_st h1))

