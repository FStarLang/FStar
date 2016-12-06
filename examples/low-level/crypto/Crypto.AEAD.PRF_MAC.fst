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

(** Start: postcondition of prf_mac **)

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


(** End: postcondition of prf_mac **)

(** Start: prf_mac ensures prf_mac_ensures **)

val prf_mac_wrapper:
  i:id -> t:PRF.state i -> k_0: CMA.akey t.mac_rgn i -> x:PRF.domain_mac i -> ST (CMA.state (i,x.iv))
  (requires (fun h0 -> True))
  (ensures  (fun h0 mac h1 -> prf_mac_ensures i t k_0 x h0 mac h1))
let prf_mac_wrapper i t k_0 x = 
  PRF.prf_mac i t k_0 x

(** End: prf_mac ensures prf_mac_ensures **)


(** Start: relate prf_mac_ensures to AEAD invariant **)

(*
 * For the AEAD invariant, after prf_mac, the PRF table must contain an unused mac for the nonce,
 * and no corresponding otp entries, further the AEAD invariant should hold
 *)

let unused_mac_exists (#i:id) (t:PRF.state i) (x:PRF.domain_mac i) (h:HS.mem) =
  safeId i ==>
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
  (requires (PRF.find prf_table y == None /\ entry.x.ctr <^ x.ctr))
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
  forall_intro (move_requires (frame_prf_find #i #r x prf_table entry))

val inv_after_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw)
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  (mac:CMA.state (i,x.iv))
  (h0 h1:mem) : Lemma
  (requires inv aead_st h0 /\                              //invariant holds in h0
            (safeId i ==> fresh_nonce x.iv aead_st h0) /\  //the nonce is fresh w.r.t. the AEAD table
            prf_mac_ensures i aead_st.prf k_0 x h0 mac h1) //prf_mac_ensures holds from h0 to h1

  (ensures inv aead_st h1 /\                                       //invariant holds in h1
           (safeId i ==>  //TODO: should this be authId i??      
             (let prf_table = HS.sel h1 (itable i aead_st.prf) in
	      unused_mac_exists aead_st.prf x h1 /\                //unused mac exists in the prf table
              none_above (PRF.incr i x) prf_table)))              //no otp entries exist in the prf table for this nonce
#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let inv_after_prf_mac #i #rw aead_st k_0 x mac h0 h1 =
  if safeId i
  then begin
    let aead_entries = HS.sel h0 aead_st.log in
    let prf_table = HS.sel h0 (itable i aead_st.prf) in
    assert (unused_aead_iv_for_prf prf_table x.iv h0);
    assert (refines prf_table aead_entries h0);
    frame_refines i aead_st.prf.mac_rgn prf_table aead_entries h0 h1;
    assert (refines prf_table aead_entries h1);
    let prf_table' = SeqProperties.snoc prf_table (PRF.Entry x mac) in
    //TODO: we need a lemma for this assume below
    //we need to use the pre-condition that tells us that x.iv is fresh for aead_entries
    let b = FStar.StrongExcludedMiddle.strong_excluded_middle (h0 == h1) in
    if b then
      ()
    else begin
      assume (refines prf_table' aead_entries h1);
      assume (unused_mac_exists aead_st.prf x h1); //from a find_snoc lemma and mac_is_unset
      frame_none_above_snoc (PRF.incr i x) prf_table (PRF.Entry x mac);
      //assert (none_above (PRF.incr i x) prf_table') //from initial invariant and snoc
    end
  end
