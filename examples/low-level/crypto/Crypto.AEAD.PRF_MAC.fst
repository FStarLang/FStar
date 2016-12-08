module Crypto.AEAD.PRF_MAC
open FStar.UInt32
open FStar.HyperStack
open FStar.Monotonic.RRef

open Crypto.Indexing
open Flag
open Crypto.Symmetric.PRF

open Crypto.AEAD.Invariant

module HS  = FStar.HyperStack

module MAC = Crypto.Symmetric.MAC
module PRF = Crypto.Symmetric.PRF
module CMA = Crypto.Symmetric.UF1CMA

///////////////////////////////////////////////////////////////////
// AEAD functions and lemmas related to the invariant and prf_mac
//////////////////////////////////////////////////////////////////

(*
 * There are two cases for prf_mac:
 *   Either the unset mac was already there (prf_mac_existed)
 *   Or prf_mac added a new (unset) mac entry to the PRF log (prf_mac_added)
 *)

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
      (forall (y:domain i). y <> x ==> PRF.find t0 y == PRF.find t1 y)  /\ //at most modifies t at x
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

(*
 * For the AEAD invariant, after prf_mac, the PRF table must contain an unused mac for the nonce,
 * and no corresponding otp entries, further the AEAD invariant should hold
 *)

let unused_mac_exists (#i:id) (t:PRF.state i) (x:PRF.domain_mac i) (h:HS.mem) =
  prf i ==>
    (let table = HS.sel h (PRF.itable i t) in
     match PRF.find_mac table x with
     | None     -> False                                            //the mac entry definitely exsits in the PRF log
     | Some mac -> CMA.mac_is_unset (i, x.iv) t.mac_rgn mac h)  //it is unset

private val frame_prf_find_snoc
  (#i:id)
  (#r:region)
  (x:PRF.domain i)
  (prf_table:prf_table r i)
  (entry:entry r i)
  (y:PRF.domain i{y `PRF.above` x}) : Lemma
  (requires (PRF.find prf_table y == None /\
             entry.x.ctr <^ x.ctr))
  (ensures  (PRF.find (SeqProperties.snoc prf_table entry) y == None))
let frame_prf_find_snoc #i #r x prf_table entry y = SeqProperties.find_snoc prf_table entry (is_entry_domain y)

private val frame_none_above_snoc
  (#i:id)
  (#r:region)
  (x:PRF.domain i)
  (prf_table:prf_table r i)
  (entry:entry r i) : Lemma
  (requires (none_above x prf_table /\  
             entry.x.ctr <^ x.ctr))
  (ensures  (none_above x (SeqProperties.snoc prf_table entry)))
let frame_none_above_snoc #i #r x prf_table entry =
  let open FStar.Classical in
  forall_intro (move_requires (frame_prf_find_snoc #i #r x prf_table entry))

private val none_above_otp_after_prf_mac
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
  (ensures  (safeMac i ==>
              (let prf_table_1 = HS.sel h1 (PRF.itable i aead_st.prf) in
               none_above (PRF.incr i x) prf_table_1)))
let none_above_otp_after_prf_mac #i #rw aead_st k_0 x mac h0 h1 =
  if safeMac i then begin
    let prf_table_0 = HS.sel h0 (itable i aead_st.prf) in 
    (match find_mac prf_table_0 x with
     | Some _ -> ()
     | None   -> frame_none_above_snoc (PRF.incr i x) prf_table_0 (PRF.Entry x mac))
  end

val unused_mac_exists_after_prf_mac
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
  (ensures (safeMac i ==> unused_mac_exists aead_st.prf x h1))
let unused_mac_exists_after_prf_mac #i #rw aead_st k_0 x mac h0 h1 = ()

let aead_inv_after_prf_mac (#i:id) (#rw:rw) (aead_st:aead_state i rw) (x:PRF.domain_mac i) (h:mem) =
  safeMac i ==>
    (let prf_table = HS.sel h (itable i aead_st.prf) in
     unused_mac_exists aead_st.prf x h /\        //unused mac exists in the prf table
     none_above (PRF.incr i x) prf_table)       //no otp entries exist in the prf table for this nonce
  
val lemma_aead_inv_after_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw)
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  (mac:CMA.state (i,x.iv))
  (h0 h1:mem) : Lemma
  (requires inv aead_st h0 /\                                  //invariant holds in h0
            fresh_nonce_st x.iv aead_st h0 /\                  //the nonce is fresh w.r.t. the AEAD table
            prf_mac_ensures i aead_st.prf k_0 x h0 mac h1)     //prf_mac_ensures holds from h0 to h1
  (ensures  (aead_inv_after_prf_mac aead_st x h1))  //TODO: inv aead_st h1
let lemma_aead_inv_after_prf_mac #i #rw aead_st k_0 x mac h0 h1 =
  if safeMac i
  then begin
    unused_mac_exists_after_prf_mac aead_st k_0 x mac h0 h1;
    none_above_otp_after_prf_mac aead_st k_0 x mac h0 h1
  end

val prf_mac_wrapper
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw)
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  : ST (CMA.state (i,x.iv))
       (requires (fun h0 -> inv aead_st h0 /\
                         fresh_nonce_st x.iv aead_st h0))
       (ensures (fun h0 mac h1 -> prf_mac_ensures i aead_st.prf k_0 x h0 mac h1 /\
                               aead_inv_after_prf_mac aead_st x h1))
let prf_mac_wrapper #i #rw aead_st k_0 x =
  let h0 = get () in
  
  let mac = PRF.prf_mac i aead_st.prf k_0 x in

  let h1 = get () in
  lemma_aead_inv_after_prf_mac aead_st k_0 x mac h0 h1;

  mac

val lemma_prf_find_append
  (#r:region)
  (#i:id)
  (table:prf_table r i)
  (blocks:prf_table r i)
  (x:PRF.domain i) : Lemma
  (requires (Some? (PRF.find table x)))
  (ensures  (PRF.find (Seq.append table blocks) x == PRF.find table x))
let lemma_prf_find_append #r #i table blocks x = SeqProperties.find_append_some table blocks (is_entry_domain x)

val lemma_prf_find_append_forall
  (#r:region)
  (#i:id)
  (table:prf_table r i)
  (blocks:prf_table r i) : Lemma
  (forall (x:PRF.domain i).{:pattern (PRF.find (Seq.append table blocks) x) }
     (Some? (PRF.find table x)) ==>
       (PRF.find (Seq.append table blocks) x == PRF.find table x))
let lemma_prf_find_append_forall #r #i table blocks =
  let open FStar.Classical in
  forall_intro (move_requires (lemma_prf_find_append #r #i table blocks))

open Crypto.AEAD.Encoding
open Crypto.Plain
open Crypto.Symmetric.Bytes

let frame_mac_is_set_append
  (#r:region)
  (#i:id)
  (table:prf_table r i{mac_log})
  (iv:Crypto.Symmetric.Cipher.iv (alg i))
  (ad:adata)
  (l:plainLen)
  (cipher:lbytes l)
  (tag:MAC.tag)
  (h:mem)
  (blocks:prf_table r i) : Lemma
  (requires (mac_is_set table iv ad l cipher tag h))
  (ensures  (mac_is_set (Seq.append table blocks) iv ad l cipher tag h))
  = lemma_prf_find_append_forall #r #i table blocks

let frame_refines_one_entry_append
  (#r:region)
  (#i:id)
  (table:prf_table r i{safeId i})
  (h:mem)
  (aead_entry:aead_entry i)
  (blocks:prf_table r i) : Lemma
  (requires (refines_one_entry table aead_entry h))
  (ensures  (refines_one_entry (Seq.append table blocks) aead_entry h))
  = lemma_prf_find_append_forall #r #i table blocks

(* let frame_mac_is_set_snoc_iv *)
(*   (#r:region) *)
(*   (#i:id) *)
(*   (prf_table:prf_table r i{safeId i}) *)
(*   (iv:Crypto.Symmetric.Cipher.iv (alg i)) *)
(*   (ad:adata) *)
(*   (l:plainLen) *)
(*   (cipher:lbytes l) *)
(*   (tag:MAC.tag) *)
(*   (h:mem) *)
(*   (entry:entry r i) : Lemma *)
(*   (requires (mac_is_set prf_table iv ad l cipher tag h /\ *)
(*              iv <> entry.x.iv)) *)
(*   (ensures  (mac_is_set (SeqProperties.snoc prf_table entry) iv ad l cipher tag h)) *)
(*   = let dom_0 = {iv = iv; ctr = PRF.ctr_0 i} in *)
(*     SeqProperties.find_snoc prf_table entry (is_entry_domain dom_0) *)

(* let rec lemma_counterblocks_iv *)
(*   (i:id{safeId i}) *)
(*   (r:eternal_region) *)
(*   (x:PRF.domain i{PRF.ctr_0 i <^ PRF.(x.ctr)}) *)
(*   (l:nat) *)
(*   (from_pos:nat) *)
(*   (to_pos:nat{from_pos <= to_pos /\ to_pos <= l /\ safelen i (to_pos - from_pos) PRF.(x.ctr)}) *)
(*   (plain:Crypto.Plain.plain i l) *)
(*   (cipher:lbytes l) : Lemma *)
(*   (requires True) *)
(*   (ensures (let otp_entries = counterblocks i r x l from_pos to_pos plain cipher in *)
(*             forall (prf_entry:entry r i). *)
(*               otp_entries `SeqProperties.contains` prf_entry ==> prf_entry.x.iv = x.iv)) *)
(*   (decreases (to_pos - from_pos)) *)
(*   = let blockl = v (Crypto.Symmetric.Cipher.(blocklen (cipherAlg_of_id i))) in *)
(*     let remaining = to_pos - from_pos in *)
(*     if remaining = 0 then SeqProperties.lemma_contains_empty #(entry r i) *)
(*     else *)
(*       let l0 = minNat remaining blockl in *)
(*       let l_32 = UInt32.uint_to_t l0 in *)
(*       let plain_hd = Crypto.Plain.slice plain from_pos (from_pos + l0) in *)
(*       let cipher_hd = Seq.slice cipher from_pos (from_pos + l0) in *)
(*       let block = PRF.Entry x (PRF.OTP l_32 plain_hd cipher_hd) in  *)
(*       let blocks = counterblocks i r (PRF.incr i x) l (from_pos + l0) to_pos plain cipher in *)
(*       lemma_counterblocks_iv i r (PRF.incr i x) l (from_pos + l0) to_pos plain cipher; *)
(*       SeqProperties.lemma_contains_singleton block; *)
(*       FStar.Classical.forall_intro (SeqProperties.append_contains_equiv (Seq.create 1 block) blocks) *)


