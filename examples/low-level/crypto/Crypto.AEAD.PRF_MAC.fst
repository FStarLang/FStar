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

(*
 * AR: this should be an easy proof, but does not go through.
 *)
private val lemma_aead_entries_are_same_after_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw{safeMac i})
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  (h0 h1:mem)
  (mac:CMA.state (i, x.iv)) : Lemma
  (requires (prf_mac_ensures i aead_st.prf k_0 x h0 mac h1))
  (ensures  (let entries_0 = HS.sel #(aead_entries i) h0 aead_st.log in
             let entries_1 = HS.sel #(aead_entries i) h1 aead_st.log in
	     entries_0 == entries_1))
let lemma_aead_entries_are_same_after_prf_mac #i #rw aead_st k_0 x h0 h1 mac = admit ()

private val frame_fresh_nonce_st_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw{safeMac i})
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  (h0 h1:mem)
  (mac:CMA.state (i, x.iv))
  (iv:Cipher.iv (alg i)) : Lemma
  (requires (prf_mac_ensures i aead_st.prf k_0 x h0 mac h1))
  (ensures  (fresh_nonce_st iv aead_st h0 <==> fresh_nonce_st iv aead_st h1))
let frame_fresh_nonce_st_prf_mac #i #rw aead_st k_0 x h0 h1 mac iv =
  lemma_aead_entries_are_same_after_prf_mac aead_st k_0 x h0 h1 mac

(*
 * For the AEAD invariant, after prf_mac, the PRF table must contain an unused mac for the nonce,
 * further the AEAD invariant should hold (which should give us no otp entries for the nonce also)
 *)

let unused_mac_exists (#i:id) (t:PRF.state i) (x:PRF.domain_mac i) (h:HS.mem) =
  prf i ==>
    (let table = HS.sel h (PRF.itable i t) in
     match PRF.find_mac table x with
     | None     -> False                                            //the mac entry definitely exsits in the PRF log
     | Some mac -> CMA.mac_is_unset (i, x.iv) t.mac_rgn mac h)  //it is unset

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
  (ensures (safeMac i ==> unused_mac_exists aead_st.prf x h1))
let lemma_unused_mac_exists_after_prf_mac #i #rw aead_st k_0 x mac h0 h1 = ()

private val frame_refines_aead_entries_prf_mac
  (#i:id)
  (#rw:rw)
  (aead_st:aead_state i rw{safeMac i})
  (k_0:CMA.akey aead_st.prf.mac_rgn i)
  (x:PRF.domain_mac i)
  (h0 h1:mem)
  (mac:CMA.state (i, x.iv)) : Lemma
  (requires (let entries_0 = HS.sel #(aead_entries i) h0 aead_st.log in
	     let table_0 = HS.sel h0 (itable i aead_st.prf) in
             aead_entries_are_refined table_0 entries_0 h0 /\
	     prf_mac_ensures i aead_st.prf k_0 x h0 mac h1))
  (ensures  (let entries_1 = HS.sel #(aead_entries i) h1 aead_st.log in
	     let table_1 = HS.sel h1 (itable i aead_st.prf) in
             aead_entries_are_refined table_1 entries_1 h1))
let frame_refines_aead_entries_prf_mac #i #rw aead_st k_0 x h0 h1 mac =
  let aead_ent_0 = HS.sel #(aead_entries i) h0 aead_st.log in
  lemma_aead_entries_are_same_after_prf_mac aead_st k_0 x h0 h1 mac;
  let table_0 = HS.sel h0 (itable i aead_st.prf) in
  frame_refines_aead_entries_h i aead_st.prf.mac_rgn table_0 aead_ent_0 h0 h1;
  match PRF.find_mac table_0 x with
  | Some _ -> ()
  | None   -> frame_refines_entries_append table_0 aead_ent_0 h1 (Seq.create 1 (PRF.Entry x mac))

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
 * AR: this needs to be fixed, takes a long time.
 *)
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
let frame_unused_aead_iv_different_from_x_prf_mac #i #rw aead_st k_0 x mac h0 h1 iv = ()

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
                               (safeMac i ==> unused_mac_exists aead_st.prf x h1)))
let prf_mac_wrapper #i #rw aead_st k_0 x =
  let h0 = get () in
  
  let mac = PRF.prf_mac i aead_st.prf k_0 x in

  let h1 = get () in
  lemma_unused_mac_exists_after_prf_mac aead_st k_0 x mac h0 h1;
  frame_inv_prf_mac aead_st k_0 x h0 h1 mac;

  mac

(* val frame_inv_prf_mac *)
(*   (#i:id) *)
(*   (#rw:rw) *)
(*   (aead_st:aead_state i rw) *)
(*   (k_0:CMA.akey aead_st.prf.mac_rgn i) *)
(*   (x:PRF.domain_mac i) *)
(*   (h0 h1:mem) *)
(*   (mac:CMA.state (i, x.iv)) : Lemma *)
(*   (requires (inv aead_st h0 /\ *)
(*              prf_mac_ensures i aead_st.prf k_0 x h0 mac h1)) *)
(*   (ensures  (inv aead_st h1)) *)
(* #set-options "--z3rlimit 100" *)
(* let frame_inv_prf_mac #i #rw aead_st k_0 x h0 h1 mac = *)
(*   if safeMac i then begin *)
(*     let aead_ent_0 = HS.sel #(aead_entries i) h0 aead_st.log in *)
(*     //AR: this should just follow from modifies of prf_mac_ensures, but it takes a long time *)
(*     let _ = assume (aead_ent_0 == HS.sel #(aead_entries i) h1 aead_st.log) in *)
(*     let table_0 = HS.sel h0 (itable i aead_st.prf) in *)
(*     let table_1 = HS.sel h1 (itable i aead_st.prf) in *)
(*     frame_refines i aead_st.prf.mac_rgn table_0 aead_ent_0 h0 h1; *)
(*     (match PRF.find_mac table_0 x with *)
(*      | Some _ -> () *)
(*      | None   -> *)
(*        lemma_frame_refines_entries_append table_0 aead_ent_0 h1 (Seq.create 1 (PRF.Entry x mac)); *)
(*        assume (fresh_nonces_are_unused table_1 aead_ent_0 h1)) *)
(*   end   *)

(*   (\* if safeMac i then begin *\) *)
(*   (\*     let table_0 = HS.sel h0 (itable i aead_st.prf) in *\) *)
(*   (\*     let aead_entries = HS.sel h0 aead_st.log in *\) *)
(*   (\*     frame_refines i aead_st.prf.mac_rgn table_0 aead_entries h0 h1; *\) *)
(*   (\*     let table_1 = HS.sel h1 (itable i aead_st.prf) in *\) *)
(*   (\*     match find_mac table_0 x with *\) *)
(*   (\*     | Some _ -> () *\) *)
(*   (\*     | None   -> *\) *)
(*   (\*       frame_refines_entries_append table_0 aead_entries h1 (Seq.create 1 (PRF.Entry x mac)); *\) *)
(*   (\*     	let open FStar.Classical in *\) *)
(*   (\*     	forall_intro (move_requires (frame_unused_aead_iv_for_prf_mac aead_st k_0 x h0 h1 mac)); *\) *)
(*   (\* 	admit () *\) *)
(*   (\*   end *\) *)
  


(* val lemma_prf_find_append_none_in_s2 *)
(*   (#r:region) *)
(*   (#i:id) *)
(*   (table:prf_table r i) *)
(*   (blocks:prf_table r i) *)
(*   (x:PRF.domain i) : Lemma *)
(*   (requires (None? (PRF.find blocks x))) *)
(*   (ensures (PRF.find (Seq.append table blocks) x == PRF.find table x)) *)
(* let lemma_prf_find_append_none_in_s2 #r #i table blocks x = *)
(*   let b = PRF.find table x in *)
(*   if Some? b then SeqProperties.find_append_some table blocks (is_entry_domain x) *)
(*   else SeqProperties.find_append_none table blocks (is_entry_domain x) *)

(* val lemma_prf_find_append_some_forall *)
(*   (#r:region) *)
(*   (#i:id) *)
(*   (table:prf_table r i) *)
(*   (blocks:prf_table r i) : Lemma *)
(*   (forall (x:PRF.domain i).{:pattern (PRF.find (Seq.append table blocks) x) } *)
(*      (Some? (PRF.find table x)) ==> *)
(*        (PRF.find (Seq.append table blocks) x == PRF.find table x)) *)
(* let lemma_prf_find_append_some_forall #r #i table blocks = *)
(*   let open FStar.Classical in *)
(*   forall_intro (move_requires (lemma_prf_find_append_some #r #i table blocks)) *)

(* open Crypto.AEAD.Encoding *)
(* open Crypto.Plain *)
(* open Crypto.Symmetric.Bytes *)

(* let frame_refines_entries_append *)
(*   (#r:region) *)
(*   (#i:id) *)
(*   (table:prf_table r i) *)
(*   (entries:aead_entries i) *)
(*   (h:mem) *)
(*   (blocks:prf_table r i) : Lemma *)
(*   (requires (safeId i ==> (forall (aead_entry:aead_entry i).{:pattern (entries `SeqProperties.contains` aead_entry)} *)
(* 		             entries `SeqProperties.contains` aead_entry ==> *)
(* 		             refines_one_entry table aead_entry h))) *)
(*   (ensures  (safeId i ==> (forall (aead_entry:aead_entry i).{:pattern (entries `SeqProperties.contains` aead_entry)} *)
(* 		             entries `SeqProperties.contains` aead_entry ==> *)
(* 		             refines_one_entry (Seq.append table blocks) aead_entry h))) *)
(*   = lemma_prf_find_append_some_forall #r #i table blocks *)

(* type erid = r:rid{is_eternal_region r} *)

(* let mac_is_unset (i:CMA.id) (region:erid) (st:CMA.state i) m = *)
(*    CMA.(st.region) == region /\ *)
(*    Crypto.Symmetric.MAC.norm m CMA.(st.r) /\ *)
(*    Buffer.live m CMA.(st.s) /\ *)
(*    (mac_log ==> *)
(*       FStar.Monotonic.RRef.m_contains (CMA.ilog CMA.(st.log)) m /\ *)
(*       FStar.Monotonic.RRef.m_sel m (CMA.ilog CMA.(st.log)) == None) *)

(* let lemma_prf_find_singleton_blocks *)
(*   (#r:region) *)
(*   (#i:id) *)
(*   (prf_entry:PRF.entry r i) *)
(*   (x:PRF.domain i) : Lemma *)
(*   (Some? (PRF.find (Seq.create 1 prf_entry) x) <==> prf_entry.x = x) *)
(*   = () *)

(* let lemma_frame_mac_is_unset_prf_mac *)
(*   (#i:id) *)
(*   (#rw:rw) *)
(*   (aead_st:aead_state i rw{safeMac i}) *)
(*   (k_0:CMA.akey aead_st.prf.mac_rgn i) *)
(*   (x:PRF.domain_mac i) *)
(*   (h0 h1:mem) *)
(*   (mac:CMA.state (i, x.iv)) *)
(*   (iv:Crypto.Symmetric.Cipher.iv (alg i)) *)
(*   (mac_st:CMA.state (i, iv)) : Lemma *)
(*   (requires (let table = HS.sel h0 (itable i aead_st.prf) in *)
(*              prf_mac_ensures i aead_st.prf k_0 x h0 mac h1 /\ *)
(* 	     iv <> x.iv /\ *)
(* 	     CMA.mac_is_unset (i, iv) aead_st.prf.mac_rgn mac_st h0)) *)
(*   (ensures (CMA.mac_is_unset (i, iv) aead_st.prf.mac_rgn mac_st h1)) *)
(*   = () *)

(* let frame_unused_aead_iv_for_prf_mac *)
(*   (#i:id) *)
(*   (#rw:rw) *)
(*   (aead_st:aead_state i rw{safeMac i}) *)
(*   (k_0:CMA.akey aead_st.prf.mac_rgn i) *)
(*   (x:PRF.domain_mac i) *)
(*   (h0 h1:mem) *)
(*   (mac:CMA.state (i, x.iv)) *)
(*   (iv:Crypto.Symmetric.Cipher.iv (alg i)) : Lemma *)
(*   (requires (let table = HS.sel h0 (itable i aead_st.prf) in *)
(*              prf_mac_ensures i aead_st.prf k_0 x h0 mac h1 /\ *)
(*              unused_aead_iv_for_prf table iv h0)) *)
(*   (ensures  (let table = HS.sel h1 (itable i aead_st.prf) in *)
(*              unused_aead_iv_for_prf table iv h1)) *)
(*   = if prf i then begin *)
(*       let table_0 = HS.sel h0 (itable i aead_st.prf) in *)
(*       let table_1 = HS.sel h1 (itable i aead_st.prf) in       *)
(*       match find_mac table_0 x with *)
(*       | Some _ -> () *)
(*       | None   -> *)
(*         (let dom_0 = {iv=iv; ctr=PRF.ctr_0 i} in *)
(* 	 let _ = assert (none_above (PRF.incr i dom_0) table_1) in *)
(* 	 if x.iv = iv then *)
(* 	   () *)
(* 	 else *)
(* 	   let _ = lemma_prf_find_singleton_blocks #aead_st.prf.mac_rgn #i (PRF.Entry x mac) dom_0 in *)
(* 	   let _ = assert (PRF.find_mac #aead_st.prf.mac_rgn #i (Seq.create 1 (PRF.Entry x mac)) dom_0 == None) in *)
(* 	   lemma_prf_find_append_none_in_s2 table_0 (Seq.create 1 (PRF.Entry x mac)) dom_0; *)
(* 	   match PRF.find_mac table_0 dom_0 with *)
(* 	   | None    -> () *)
(* 	   | Some mr -> lemma_frame_mac_is_unset_prf_mac aead_st k_0 x h0 h1 mac iv mr) *)
(*     end *)

(* #set-options "--z3rlimit 200" *)
(* let frame_inv_prf_mac *)
(*   (#i:id) *)
(*   (#rw:rw) *)
(*   (aead_st:aead_state i rw) *)
(*   (k_0:CMA.akey aead_st.prf.mac_rgn i) *)
(*   (x:PRF.domain_mac i) *)
(*   (h0 h1:mem) *)
(*   (mac:CMA.state (i, x.iv)) : Lemma *)
(*   (requires (inv aead_st h0 /\ *)
(*              prf_mac_ensures i aead_st.prf k_0 x h0 mac h1)) *)
(*   (ensures  (inv aead_st h1)) *)
(*   = if safeMac i then begin *)
(*       let table_0 = HS.sel h0 (itable i aead_st.prf) in *)
(*       let aead_entries = HS.sel h0 aead_st.log in *)
(*       frame_refines i aead_st.prf.mac_rgn table_0 aead_entries h0 h1; *)
(*       let table_1 = HS.sel h1 (itable i aead_st.prf) in *)
(*       match find_mac table_0 x with *)
(*       | Some _ -> () *)
(*       | None   -> *)
(*         frame_refines_entries_append table_0 aead_entries h1 (Seq.create 1 (PRF.Entry x mac)); *)
(*       	let open FStar.Classical in *)
(*       	forall_intro (move_requires (frame_unused_aead_iv_for_prf_mac aead_st k_0 x h0 h1 mac)); *)
(* 	admit () *)
(*     end *)
   
(* val prf_mac_wrapper *)
(*   (#i:id) *)
(*   (#rw:rw) *)
(*   (aead_st:aead_state i rw) *)
(*   (k_0:CMA.akey aead_st.prf.mac_rgn i) *)
(*   (x:PRF.domain_mac i) *)
(*   : ST (CMA.state (i,x.iv)) *)
(*        (requires (fun h0 -> inv aead_st h0 /\ *)
(*                          fresh_nonce_st x.iv aead_st h0)) *)
(*        (ensures (fun h0 mac h1 -> prf_mac_ensures i aead_st.prf k_0 x h0 mac h1 /\ *)
(*                                aead_inv_after_prf_mac aead_st x h1 /\ *)
(* 			       inv aead_st h1)) *)
(* let prf_mac_wrapper #i #rw aead_st k_0 x = *)
(*   let h0 = get () in *)
  
(*   let mac = PRF.prf_mac i aead_st.prf k_0 x in *)

(*   let h1 = get () in *)
(*   lemma_aead_inv_after_prf_mac aead_st k_0 x mac h0 h1; *)
(*   frame_inv_prf_mac aead_st k_0 x h0 h1 mac; *)

(*   mac *)

(* private val frame_prf_find_snoc *)
(*   (#i:id) *)
(*   (#r:region) *)
(*   (x:PRF.domain i) *)
(*   (prf_table:prf_table r i) *)
(*   (entry:entry r i) *)
(*   (y:PRF.domain i{y `PRF.above` x}) : Lemma *)
(*   (requires (PRF.find prf_table y == None /\ *)
(*              entry.x.ctr <^ x.ctr)) *)
(*   (ensures  (PRF.find (SeqProperties.snoc prf_table entry) y == None)) *)
(* let frame_prf_find_snoc #i #r x prf_table entry y = SeqProperties.find_snoc prf_table entry (is_entry_domain y) *)


(* AR: Moving these as part of cleanup, we now have inv, so we should be able to show none_above_otp directly *)

(* begin *)

(* private val frame_none_above_snoc *)
(*   (#i:id) *)
(*   (#r:region) *)
(*   (x:PRF.domain i) *)
(*   (prf_table:prf_table r i) *)
(*   (entry:entry r i) : Lemma *)
(*   (requires (none_above x prf_table /\   *)
(*              entry.x.ctr <^ x.ctr)) *)
(*   (ensures  (none_above x (SeqProperties.snoc prf_table entry))) *)
(* let frame_none_above_snoc #i #r x prf_table entry = *)
(*   let open FStar.Classical in *)
(*   forall_intro (move_requires (frame_prf_find_snoc #i #r x prf_table entry)) *)

(* private val none_above_otp_after_prf_mac *)
(*   (#i:id) *)
(*   (#rw:rw) *)
(*   (aead_st:aead_state i rw) *)
(*   (k_0:CMA.akey aead_st.prf.mac_rgn i) *)
(*   (x:PRF.domain_mac i) *)
(*   (mac:CMA.state (i,x.iv)) *)
(*   (h0 h1:mem) : Lemma *)
(*   (requires inv aead_st h0 /\ *)
(*             (safeMac i ==> fresh_nonce_st x.iv aead_st h0) /\ *)
(*             prf_mac_ensures i aead_st.prf k_0 x h0 mac h1) *)
(*   (ensures  (safeMac i ==> *)
(*               (let prf_table_1 = HS.sel h1 (PRF.itable i aead_st.prf) in *)
(*                none_above (PRF.incr i x) prf_table_1))) *)
(* let none_above_otp_after_prf_mac #i #rw aead_st k_0 x mac h0 h1 = *)
(*   if safeMac i then begin *)
(*     let prf_table_0 = HS.sel h0 (itable i aead_st.prf) in  *)
(*     (match find_mac prf_table_0 x with *)
(*      | Some _ -> () *)
(*      | None   -> frame_none_above_snoc (PRF.incr i x) prf_table_0 (PRF.Entry x mac)) *)
(*   end *)

(* end *)


(* AR:  It's part of the same cleanup *)

(* begin *)

(* let aead_inv_after_prf_mac (#i:id) (#rw:rw) (aead_st:aead_state i rw{safeMac i}) (x:PRF.domain_mac i) (h:mem) = *)
(*   let prf_table = HS.sel h (itable i aead_st.prf) in *)
(*   unused_mac_exists aead_st.prf x h /\        //unused mac exists in the prf table *)
(*   none_above (PRF.incr i x) prf_table)       //no otp entries exist in the prf table for this nonce *)
  
(* val lemma_aead_inv_after_prf_mac *)
(*   (#i:id) *)
(*   (#rw:rw) *)
(*   (aead_st:aead_state i rw) *)
(*   (k_0:CMA.akey aead_st.prf.mac_rgn i) *)
(*   (x:PRF.domain_mac i) *)
(*   (mac:CMA.state (i,x.iv)) *)
(*   (h0 h1:mem) : Lemma *)
(*   (requires inv aead_st h0 /\                                  //invariant holds in h0 *)
(*             fresh_nonce_st x.iv aead_st h0 /\                  //the nonce is fresh w.r.t. the AEAD table *)
(*             prf_mac_ensures i aead_st.prf k_0 x h0 mac h1)     //prf_mac_ensures holds from h0 to h1 *)
(*   (ensures  (aead_inv_after_prf_mac aead_st x h1))  //TODO: inv aead_st h1 *)
(* let lemma_aead_inv_after_prf_mac #i #rw aead_st k_0 x mac h0 h1 = *)
(*   if safeMac i *)
(*   then begin *)
(*     unused_mac_exists_after_prf_mac aead_st k_0 x mac h0 h1; *)
(*     none_above_otp_after_prf_mac aead_st k_0 x mac h0 h1 *)
(*   end *)


(* end *)
