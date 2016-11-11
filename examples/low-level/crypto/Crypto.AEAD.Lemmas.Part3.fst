(* This module includes several lemmas to work with the 
   invariants defined in Crypto.AEAD.Invariant *)
module Crypto.AEAD.Lemmas.Part3
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.Monotonic.RRef

open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Crypto.Plain
open Flag

open Crypto.Symmetric.PRF
open Crypto.AEAD.Encoding 
open Crypto.AEAD.Invariant

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module MAC = Crypto.Symmetric.MAC
module CMA = Crypto.Symmetric.UF1CMA

module Plain = Crypto.Plain
module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF

open Crypto.AEAD.Lemmas
open Crypto.AEAD.Lemmas.Part2

let modifies_push_pop (h:HS.mem) (h0:HS.mem) (h5:HS.mem) (r:Set.set HH.rid)
  : Lemma (requires (HS.fresh_frame h h0 /\
		     HS.modifies_transitively (Set.union r (Set.singleton (HS h0.tip))) h0 h5))
          (ensures (HS.poppable h5 /\ HS.modifies_transitively r h (HS.pop h5)))
  = ()

let frame_myinv_push (#i:id) (#rw:rw) (st:state i rw) (h:mem) (h1:mem)
   : Lemma (requires (my_inv st h /\ 
		      HS.fresh_frame h h1))
	   (ensures (my_inv st h1))
   = if safeId i
     then frame_refines i st.prf.mac_rgn (HS.sel h st.log) (HS.sel h (PRF.itable i st.prf)) h h1

#reset-options "--z3timeout 400 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
val refines_to_inv: (i:id) -> (st:state i Writer) -> (nonce:Cipher.iv (alg i)) ->
		       (aadlen: UInt32.t {aadlen <=^ aadmax}) ->
		       (aad: lbuffer (v aadlen)) ->
		       (len: UInt32.t {len <> 0ul}) ->
		       (plain:plainBuffer i (v len)) -> 
		       (cipher:lbuffer (v len + v MAC.taglen)) ->
    ST unit (requires (fun h1 ->
		      Buffer.live h1 aad /\ 
		      Plain.live h1 plain /\ 
		      Buffer.live h1 cipher /\ (
		      HS (h1.h) `Map.contains` st.prf.mac_rgn /\
		      h1 `HS.contains` st.log /\
		      (safeId i ==> (
			let mac_rgn = st.prf.mac_rgn in
      			let entries_0 = HS.sel h1 st.log in 
			let table_1 = HS.sel h1 (PRF.itable i st.prf) in
     			let p = Plain.sel_plain h1 len plain in
			let c_tagged = Buffer.as_seq h1 cipher in
			let c, tag = SeqProperties.split c_tagged (v len) in
			let ad = Buffer.as_seq h1 aad in
  			let entry = Entry nonce ad (v len) p c_tagged in
			h1 `HS.contains` (itable i st.prf) /\
			refines h1 i mac_rgn (SeqProperties.snoc entries_0 entry) table_1)))))
          (ensures (fun h1 _ h2 -> 
      		      Buffer.live h1 aad /\ 
		      Plain.live h1 plain /\ 
		      Buffer.live h1 cipher /\ (
		      inv h2 st /\
		      (if safeId i then 
			let mac_rgn = st.prf.mac_rgn in
      			let entries_0 = HS.sel h1 st.log in 
			let table_1 = HS.sel h1 (PRF.itable i st.prf) in
     			let p = Plain.sel_plain h1 len plain in
			let c_tagged = Buffer.as_seq h1 cipher in
			let c, tag = SeqProperties.split c_tagged (v len) in
			let ad = Buffer.as_seq h1 aad in
  			let entry = Entry nonce ad (v len) p c_tagged in
  			HS.modifies (Set.singleton st.log_region) h1 h2 /\
			HS.modifies_ref st.log_region !{HS.as_ref st.log} h1 h2 /\ 
			HS.sel h2 st.log == SeqProperties.snoc entries_0 entry
		      else HS.modifies Set.empty h1 h2))))
let refines_to_inv i st nonce aadlen aad len plain cipher =
  if safeId i then
    let h0 = get () in 
    let ad = to_seq_temp aad aadlen in
    let p = Plain.load len plain in 
    let c_tagged = to_seq_temp cipher len in
    let entry = Entry nonce ad (v len) p c_tagged in
    st.log := SeqProperties.snoc !st.log entry;
    let h1 = get () in 
    let entries = !st.log in
    let blocks = !(itable i st.prf) in
    frame_refines i st.prf.mac_rgn entries blocks h0 h1
  else ()

let lemma_frame_find_mac (#i:id) (#l:nat) (st:PRF.state i) 
			 (x:PRF.domain i{ctr_0 i <^ x.ctr}) (b:lbuffer l)
			 (h0:HS.mem) (h1:HS.mem) 
    : Lemma (requires (modifies_table_above_x_and_buffer st x b h0 h1))
	    (ensures (prf i ==> (
		      let r = PRF.itable i st in
		      let tab0 = HS.sel h0 r in
		      let tab1 = HS.sel h1 r in
		      let x0 = {x with ctr=ctr_0 i} in
		      find_mac tab0 x0 == find_mac tab1 x0)))
    = if prf i
      then begin
	let r = PRF.itable i st in
	let tab_0 = HS.sel h0 r in
	let tab_1 = HS.sel h1 r in
	let x0 = {x with ctr=ctr_0 i} in
	let tl_tab_1 = Seq.slice tab_1 (Seq.length tab_0) (Seq.length tab_1) in
	assert (Seq.equal tab_1 (Seq.append tab_0 tl_tab_1));
	match find tab_0 x0 with 
	| Some _ -> find_blocks_append_l tab_0 tl_tab_1 x0
	| _ -> find_mac_counterblocks_none x0.iv tl_tab_1;
	      find_append x0 tab_0 tl_tab_1
      end

open FStar.Heap
let modifies_fresh_empty (i:id) (n: Cipher.iv (alg i)) (r:rid) (m:CMA.state (i,n)) 
			 (h0:mem) (h1:mem) (h2:mem) 
  : Lemma (requires (HS (h0.h) `Map.contains` r /\
		     HS.modifies_ref r TSet.empty h0 h1 /\
		    (mac_log ==> 
		        (let ref = CMA (as_hsref (ilog m.log)) in
			 HS.frameOf ref == r /\
			 HS.modifies_ref r (TSet.singleton (HS.as_aref ref)) h1 h2)) /\
		    (safeId i ==> ~ (m_contains (CMA (ilog m.log)) h0))))
          (ensures (safeId i ==> HS.modifies_ref r TSet.empty h0 h2))
  = ()

