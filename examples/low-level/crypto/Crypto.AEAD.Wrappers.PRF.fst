module Crypto.AEAD.Wrappers.PRF
open FStar.UInt32
open FStar.HyperStack
open FStar.HyperStack.ST
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
module ST  = FStar.HyperStack.ST

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
      t1 == Seq.snoc t0 (PRF.Entry x returned_mac) /\ //precisely extended the table with 1 new entry
      CMA.genPost (i,x.iv) t.mac_rgn h0 returned_mac h1      /\ //the mac is freshly generated (and unset)
      HS.modifies_transitively (Set.singleton t.rgn) h0 h1   /\ //only touched the prf's region (and its children)
      HS.modifies_ref t.rgn (Set.singleton (Heap.addr_of (HS.as_ref r))) h0 h1             /\ //in the prf region, only modified the table
      HS.modifies_ref t.mac_rgn Set.empty h0 h1               //in the mac region, didn't touch any existing ref
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
      HS.modifies_ref t.rgn Set.empty h0 h1  /\              //but nothing within it is modified
      HS.modifies_ref t.mac_rgn Set.empty h0 h1

(*****)

(*
 * AEAD entries remain same after prf mac, separating it makes things go a bit faster
 *)
private val lemma_aead_entries_are_same_after_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw{safeMac i})
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  (h0 h1:mem)
  (mac:CMA.state (i, x.iv)) : Lemma
  (requires
     (h0 `HS.contains` (st_ilog aead_st) /\            //initial heap contains the aead log
      prf_mac_ensures i aead_st.prf k_0 x h0 mac h1))   //h0 and h1 are related by prf_mac_ensures
  (ensures  (let entries_0 = HS.sel #(aead_entries i) h0 (st_ilog aead_st) in
             let entries_1 = HS.sel #(aead_entries i) h1 (st_ilog aead_st) in
	     entries_0 == entries_1))  //aead entries are same in h0 and h1
let lemma_aead_entries_are_same_after_prf_mac #i #rw aead_st k_0 x h0 h1 mac = ()

(*
 * Freshness of nonces is preserved by prf_mac, follows the from preservation of aead entries by prf_mac
 *)
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
             (let entries_0 = HS.sel #(aead_entries i) h0 (st_ilog aead_st) in
	      let table_0 = HS.sel h0 (itable i aead_st.prf) in
              aead_entries_are_refined table_0 entries_0 h0 /\
	      prf_mac_ensures i aead_st.prf k_0 x h0 mac h1)))
  (ensures  (let entries_1 = HS.sel #(aead_entries i) h1 (st_ilog aead_st) in
	     let table_1 = HS.sel h1 (itable i aead_st.prf) in
             aead_entries_are_refined table_1 entries_1 h1))
let frame_refines_aead_entries_prf_mac #i #rw aead_st k_0 x h0 h1 mac =
  let aead_ent_0 = HS.sel #(aead_entries i) h0 (st_ilog aead_st) in
  //this is recalling that aead_entries are not changed from h0 to h1, makes the proof go faster
  lemma_aead_entries_are_same_after_prf_mac aead_st k_0 x h0 h1 mac;
  
  let table_0 = HS.sel h0 (itable i aead_st.prf) in
  match PRF.find_mac table_0 x with
  | Some _ -> ()
  | None   ->
    frame_refines_entries_h i aead_st.prf.mac_rgn table_0 aead_ent_0 h0 h1;
    frame_refines_entries_prf_append table_0 aead_ent_0 h1 (Seq.create 1 (PRF.Entry x mac))

(*
 * unused_aead_iv_for_prf for x.iv is preserved by prf_mac
 * since prf_mac does not add any otp entries, and leaves an unset mac entry for x.iv after completion
 *)
private val frame_unused_aead_iv_for_prf_x_prf_mac
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
let frame_unused_aead_iv_for_prf_x_prf_mac #i #rw aead_st k_0 x mac h0 h1 = ()

(*
 * unused_aead_iv_for_prf for any iv <> x.iv is preserved by prf_mac
 * since prf_mac does not add any entries in the prf table for iv <> x.iv, and does not modify existing references in the mac_rgn
 *)
private val frame_unused_aead_iv_for_prf_different_from_x_prf_mac
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
	     iv <> x.iv))
  (ensures  (let table_1 = HS.sel h1 (itable i aead_st.prf) in
             unused_aead_iv_for_prf table_1 iv h1))
let frame_unused_aead_iv_for_prf_different_from_x_prf_mac #i #rw aead_st k_0 x mac h0 h1 iv =
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

(*
 * for all fresh nonces, unused_aead_iv_for_prf holds after prf_mac
 * case analysis on iv = x.iv or iv <> x.iv
 *)
private val frame_unused_aead_iv_for_prf_prf_mac
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
let frame_unused_aead_iv_for_prf_prf_mac #i #rw aead_st k_0 x mac h0 h1 iv =
  if iv = x.iv then frame_unused_aead_iv_for_prf_x_prf_mac #i #rw aead_st k_0 x mac h0 h1
  else              frame_unused_aead_iv_for_prf_different_from_x_prf_mac #i #rw aead_st k_0 x mac h0 h1 iv

(*
 * framing of fresh_nonces_are_unused by prf_mac
 * the proof follows from:
     -- a nonce fresh before prf_mac is fresh after prf_mac (frame_fresh_nonce_st_prf_mac)
     -- if unused_aead_iv_for_prf for a fresh nonce before prf_mac (ensured by inv), then unused_aead_iv_for_prf for that nonce
        after prf_mac (frame_unused_aead_iv_for_prf_prf_mac)
 *)
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
  (ensures  (let entries_1 = HS.sel #(aead_entries i) h1 (st_ilog aead_st) in
	     let table_1 = HS.sel h1 (itable i aead_st.prf) in
             fresh_nonces_are_unused table_1 entries_1 h1))
let frame_fresh_nonces_are_unused_prf_mac #i #rw aead_st k_0 x h0 h1 mac =
  let open FStar.Classical in
  forall_intro (move_requires (frame_fresh_nonce_st_prf_mac aead_st k_0 x h0 h1 mac));
  forall_intro (move_requires (frame_unused_aead_iv_for_prf_prf_mac aead_st k_0 x mac h0 h1))

(*
 * framing of inv by prf_mac
 *)
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

private val prf_mac_find_unchanged (#i:id) (#rw:rw) (aead_st:aead_state i rw)
			           (k_0:CMA.akey aead_st.prf.mac_rgn i)
			           (x:PRF.domain_mac i)
			           (h0:mem) (h1:mem) (e:PRF.entry aead_st.prf.mac_rgn i)
   : Lemma (requires (let open PRF in
		      prf i /\ (
		      let t0 = HS.sel h0 (itable i aead_st.prf) in
		      let t1 = HS.sel h1 (itable i aead_st.prf) in
		      e.x == x /\
		      t1 == Seq.snoc t0 e)))
           (ensures (let open PRF in
		     prf i /\ (
		     let t0 = HS.sel h0 (itable i aead_st.prf) in
		     let t1 = HS.sel h1 (itable i aead_st.prf) in
		     forall (y:domain i). y <> x ==> PRF.find t0 y == PRF.find t1 y)))
let prf_mac_find_unchanged #i #rw aead_st k_0 x h0 h1 e =
  let t0 = HS.sel h0 (itable i aead_st.prf) in
  let t1 = HS.sel h1 (itable i aead_st.prf) in  
  let aux (y:domain i) : Lemma (y <> x ==> PRF.find t0 y == PRF.find t1 y) =
    FStar.Seq.find_snoc t0 e (is_entry_domain y) 
  in
  FStar.Classical.forall_intro aux

(*+ prf_mac_0: 
      Strengthening the spec of PRF.prf_mac to show that 
      it leaves the table unchanged except at one location
 *)      
private val prf_mac_0
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw)
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  : ST (CMA.state (i,x.iv))
       (requires (fun h0 -> True))
       (ensures (fun h0 mac h1 -> prf_mac_ensures i aead_st.prf k_0 x h0 mac h1))
let prf_mac_0 #i #rw aead_st k_0 x =
  let h0 = get () in
  let mac = PRF.prf_mac i aead_st.prf k_0 x in
  let h1 = get () in
  if prf i then begin
     let open FStar.Classical in 
     forall_intro (move_requires (prf_mac_find_unchanged aead_st k_0 x h0 h1))
  end;
  mac

(*+ prf_mac_enc:
      A wrapper for PRF.prf_mac, specialized for its use in AEAD.Encrypt.encrypt
**)      
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
		   enc_dec_separation aead_st aad plain cipher_tagged /\    //separation invariants
		   enc_dec_liveness aead_st aad plain cipher_tagged h0 /\   //liveness invariants hold in h0
		   inv aead_st h0 /\                                        //main stateful invariant holds in h0
                   (safeMac i ==> fresh_nonce_st x.iv aead_st h0)))        //x.iv is fresh for aead_st in h0
       (ensures (fun h0 ak h1 -> 
       		   enc_dec_liveness aead_st aad plain cipher_tagged h1 /\                        //liveness invariants hold in h1
		   prf_mac_ensures i aead_st.prf k_0 x h0 ak h1 /\                                //h0 and h1 are related by prf_mac_ensures
		   BufferUtils.prf_mac_modifies aead_st.log_region aead_st.prf.mac_rgn h0 h1 /\  //prf_mac only touches the prf region and children, and does not modify any existing reference in the mac region
   		   ak_live PRF.(aead_st.prf.mac_rgn) ak h1 /\                                    //ak_live
		   inv aead_st h1 /\                                                             //prf_mac preserves the main stateful invariant
                   (safeMac i ==>
		    (let table_1 = HS.sel h1 (itable i aead_st.prf) in
		     fresh_nonce_st x.iv aead_st h1 /\                                           //x.iv is still fresh in h1 (no modifications to the aead log)
		     is_mac_for_iv aead_st ak h1 /\                                              //ak is the mac entry for x.iv in the prf table
		     unused_mac_exists table_1 x h1 /\                                            //unused mac exists in the prf table
		     none_above (PRF.incr i x) table_1))))                                       //no otp entries after prf_mac
let prf_mac_enc #i #rw aead_st #aadlen aad #len plain cipher_tagged k_0 x = 
 let h0 = get () in
 let ak = prf_mac_0 aead_st k_0 x in
 let h1 = get () in
 lemma_unused_mac_exists_after_prf_mac aead_st k_0 x ak h0 h1;
 frame_inv_prf_mac aead_st k_0 x h0 h1 ak;
 if safeMac i then frame_fresh_nonce_st_prf_mac aead_st k_0 x h0 h1 ak x.iv;
 BufferUtils.intro_prf_mac_modifies aead_st.log_region aead_st.prf.mac_rgn h0 h1;
 ak

(*+ prf_mac_dec:
      A wrapper for PRF.prf_mac, specialized for its use in AEAD.Decrypt.decrypt
**)      
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
  let ak = prf_mac_0 aead_st k_0 x in
  let h1 = get () in
  frame_inv_prf_mac aead_st k_0 x h0 h1 ak;
  BufferUtils.intro_prf_mac_modifies aead_st.log_region aead_st.prf.mac_rgn h0 h1;
  ak
