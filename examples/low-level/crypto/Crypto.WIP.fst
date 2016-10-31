module Crypto.WIP

// We implement ideal AEAD on top of ideal Chacha20 and ideal Poly1305. 
// We precisely relate AEAD's log to their underlying state.

// This file intends to match the spec of AEAD0.fst in mitls-fstar. 

open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.Monotonic.RRef

open Crypto.Symmetric.Bytes
open Plain
open Flag

open Crypto.Symmetric.PRF
open Crypto.AEAD.Encoding 
open Crypto.AEAD.Invariant
open Crypto.AEAD.Lemmas
open Crypto.AEAD.Lemmas.Part2
open Crypto.AEAD

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module Spec = Crypto.Symmetric.Poly1305.Spec
module MAC = Crypto.Symmetric.Poly1305.MAC

module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF

val encrypt: 
  i: id -> st:state i Writer -> 
  n: Cipher.iv (alg i) ->
  aadlen: UInt32.t {aadlen <=^ aadmax} -> 
  aad: lbuffer (v aadlen) -> 
  plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) 1ul} -> 
  plain: plainBuffer i (v plainlen) -> 
  cipher:lbuffer (v plainlen + v (Spec.taglen i)) 
  { 
    Buffer.disjoint aad cipher /\
    Buffer.disjoint (Plain.as_buffer plain) aad /\
    Buffer.disjoint (Plain.as_buffer plain) cipher /\
    HH.disjoint (Buffer.frameOf (Plain.as_buffer plain)) st.log_region /\
    HH.disjoint (Buffer.frameOf cipher) st.log_region /\
    HH.disjoint (Buffer.frameOf aad) st.log_region
  }
  ->  
  //STL -- should be STL eventually, but this requires propagation throughout the library
  ST unit
  (requires (fun h -> 
    let prf_rgn = st.prf.rgn in
    Crypto.AEAD.inv h #i #Writer st /\
    Buffer.live h aad /\
    Buffer.live h cipher /\ 
    Plain.live h plain /\
    (prf i ==> none_above ({iv=n; ctr=0ul}) st.prf h) // The nonce must be fresh!
   ))
  (ensures (fun h0 _ h1 -> 
    //TODO some "heterogeneous" modifies that also records updates to logs and tables
    Buffer.modifies_1 cipher h0 h1 /\ 
    Buffer.live h1 aad /\
    Buffer.live h1 cipher /\ 
    Plain.live h1 plain /\
    inv h1 #i #Writer st /\ 
    (safeId i ==> (
      let aad = Buffer.as_seq h1 aad in
      let p = Plain.sel_plain h1 plainlen plain in
      let c = Buffer.as_seq h1 cipher in
      HS.sel h1 st.log == SeqProperties.snoc (HS.sel h0 st.log) (Entry n aad (v plainlen) p c)))
   ))

(* #reset-options "--z3timeout 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0" *)
(* let test (h0:HS.mem) (h1:HS.mem) (r:rid) =  *)
(*   let open FStar.HyperStack in  *)
(*   assume (r `HS.is_in` h0.h); *)
(*   assume (Buffer.modifies_0 h0 h1); *)
(*   Buffer.lemma_reveal_modifies_0 h0 h1; *)
(*   assume (r <> h0.tip); *)
(*   assert (Map.sel h1.h r == Map.sel h0.h r) *)
  
(* assume val temp_to_seq: #a:Type -> b:Buffer.buffer a -> ST (Seq.seq a) *)
(*   (requires (fun h -> Buffer.live h b)) *)
(*   (ensures  (fun h0 r h1 -> h0 == h1 /\ Buffer.live h1 b /\r == Buffer.as_seq #a h1 b)) *)

(* assume val temp_get_plain: #i:id -> #l:UInt32.t -> buf:plainBuffer i (v l) -> ST (plain i (v l)) *)
(*   (requires (fun h -> Plain.live h buf)) *)
(*   (ensures (fun h0 p h1 -> h0==h1 /\ Plain.live h0 buf /\p == Plain.sel_plain h1 l buf)) *)

let lemma_frame_find_mac (#i:PRF.id) (#l:nat) (st:PRF.state i) 
			 (x:PRF.domain i{x.ctr <> 0ul}) (b:lbuffer l)
			 (h0:HS.mem) (h1:HS.mem) 
    : Lemma (requires (modifies_table_above_x_and_buffer st x b h0 h1))
	    (ensures (prf i ==> (
		      let r = PRF.itable i st in
		      let tab0 = HS.sel h0 r in
		      let tab1 = HS.sel h1 r in
		      let x0 = {x with ctr=0ul} in
		      find_mac tab0 x0 == find_mac tab1 x0)))
    = admit()		      

open FStar.Heap
let heap_modifies_fresh_empty_0  (h0:heap) (h1:heap) (h2:heap) (x:FStar.Heap.ref nat)
  : Lemma (requires (Heap.modifies TSet.empty h0 h1 /\
		     Heap.modifies !{x} h1 h2 /\
		     not(h0 `Heap.contains` x)))
          (ensures (Heap.modifies TSet.empty h0 h2))
  = ()	  

let modifies_fresh_empty_0  (h0:mem) (h1:mem) (h2:mem) (r:rid) (x:HS.reference nat)
  : Lemma (requires (HS (h0.h) `Map.contains` r /\
		     HS.modifies_ref r TSet.empty h0 h1 /\
  		     HS.modifies_ref r (TSet.singleton (HS.as_aref x)) h1 h2 /\
		     HS.frameOf x == r /\
		     ~(h0 `HS.contains` x)))
          (ensures (HS.modifies_ref r TSet.empty h0 h2))
  = ()	  
  
let modifies_fresh_empty (i:id) (n: Cipher.iv (alg i)) (r:rid) (m:MAC.state (i,n)) 
			 (h0:mem) (h1:mem) (h2:mem) 
  : Lemma (requires (HS (h0.h) `Map.contains` r /\
		     HS.modifies_ref r TSet.empty h0 h1 /\
		    (mac_log ==> 
		        (let ref = MAC (as_hsref (ilog m.log)) in
			 HS.frameOf ref == r /\
			 HS.modifies_ref r (TSet.singleton (MAC (HS.as_aref ref))) h1 h2)) /\
		    (safeId i ==> ~ (m_contains (MAC (ilog m.log)) h0))))
          (ensures (safeId i ==> HS.modifies_ref r TSet.empty h0 h2))
  = assert (safeId i ==> prf i /\ mac_log);
    ()
  
#reset-options "--z3timeout 400 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --log_queries"

val extend_refines_aux: (i:id) -> (st:state i Writer) -> (nonce:Cipher.iv (alg i)) ->
		       (aadlen: UInt32.t {aadlen <=^ aadmax}) ->
		       (aad: lbuffer (v aadlen)) ->
                       (len:nat{len<>0}) -> (plain:plainBuffer i len) -> (cipher:lbuffer (len + v (Spec.taglen i))) ->
		       (h0:mem) ->
                       (h1:mem{Buffer.live h1 aad /\ Plain.live h1 plain /\ Buffer.live h1 cipher}) ->
    Lemma (requires ( safeId i ==> (
		      let mac_rgn = st.prf.mac_rgn in
      		      let entries_0 = HS.sel h0 st.log in 
		      let blocks_0 = HS.sel h0 (PRF.itable i st.prf) in
		      let table_1 = HS.sel h1 (PRF.itable i st.prf) in
		      Seq.length table_1 > Seq.length blocks_0 /\ (
		      let blocks_1 = Seq.slice table_1 (Seq.length blocks_0) (Seq.length table_1) in

     		      let p = Plain.sel_plain h1 (u len) plain in
		      let c_tagged = Buffer.as_seq h1 cipher in
	              let c, tag = SeqProperties.split c_tagged len in
		      let ad = Buffer.as_seq h1 aad in
  		      let entry = Entry nonce ad len p c_tagged in
		      pre_refines_one_entry i st nonce len plain cipher h0 h1 /\
		      inv h0 st /\
		      refines_one_entry #_ #i h1 entry blocks_1 /\
      		      HS.modifies_ref mac_rgn TSet.empty h0 h1 /\
		      HS.live_region h1 mac_rgn))))
		      
          (ensures ( safeId i ==> (
		      let mac_rgn = st.prf.mac_rgn in
      		      let entries_0 = HS.sel h0 st.log in 
		      let table_1 = HS.sel h1 (PRF.itable i st.prf) in
     		      let p = Plain.sel_plain h1 (u len) plain in
		      let c_tagged = Buffer.as_seq h1 cipher in
	              let c, tag = SeqProperties.split c_tagged len in
		      let ad = Buffer.as_seq h1 aad in
  		      let entry = Entry nonce ad len p c_tagged in
		      refines h1 i mac_rgn (SeqProperties.snoc entries_0 entry) table_1)))
let extend_refines_aux i st nonce aadlen aad len plain cipher h0 h1 = 
  if safeId i then
     let mac_rgn = st.prf.mac_rgn in
     let entries_0 = HS.sel h0 st.log in 
     let blocks_0 = HS.sel h0 (PRF.itable i st.prf) in
     let table_1 = HS.sel h1 (PRF.itable i st.prf) in
     let blocks_1 = Seq.slice table_1 (Seq.length blocks_0) (Seq.length table_1) in
     let p = Plain.sel_plain h1 (u len) plain in
     let c_tagged = Buffer.as_seq h1 cipher in
     let c, tag = SeqProperties.split c_tagged len in
     let ad = Buffer.as_seq h1 aad in
     let entry = Entry nonce ad len p c_tagged in
     assume (pre_refines_one_entry i st nonce len plain cipher h0 h1);
     extend_refines h0 i mac_rgn entries_0 blocks_0 entry blocks_1 h1
 
let encrypt i st n aadlen aad plainlen plain cipher_tagged =
  (* push_frame(); *)
  (* assume (safeId i); *)
  (* assume (prf i); *)
  let h0 = get() in
  assume (HS (h0.h `Map.contains` st.prf.mac_rgn));
  assume (HS (HH.disjoint h0.tip st.prf.mac_rgn));
  assume (HS (is_stack_region h0.tip)); //TODO: remove this once we move all functions to STL
  let x = PRF({iv = n; ctr = 0ul}) in // PRF index to the first block
  let ak = PRF.prf_mac i st.prf x in  // used for keying the one-time MAC  
  let h1 = get () in 
  assert (HS.modifies_ref st.prf.mac_rgn TSet.empty h0 h1);
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in
  let tag = Buffer.sub cipher_tagged plainlen (Spec.taglen i) in
  let y = PRF.incr i x in
  //calling this lemma allows us to complete the proof without using any fuel;
  //which makes things a a bit faster
  counterblocks_emp i st.prf.mac_rgn y (v plainlen) 0
      (Plain.sel_plain h1 plainlen plain) (Buffer.as_seq h1 cipher);
  counter_enxor i st.prf y plainlen plainlen plain cipher h1;
  // Compute MAC over additional data and ciphertext
  let h2 = get () in
  FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 cipher h1) h2;
  assert (HS.modifies_ref st.prf.mac_rgn TSet.empty h0 h2);
  lemma_frame_find_mac #i #(v plainlen) st.prf y cipher h1 h2;
  intro_refines_one_entry_no_tag #i st n (v plainlen) plain cipher_tagged h0 h1 h2; //we have pre_refines_one_entry here
  assert (Buffer.live h1 aad); //seem to need this hint
  let l, acc = accumulate ak aadlen aad plainlen cipher in
  let h3 = get() in
  Buffer.lemma_reveal_modifies_0 h2 h3;
  assert (HS.modifies_ref st.prf.mac_rgn TSet.empty h0 h3);
  frame_pre_refines_0 i st n (v plainlen) plain cipher_tagged h0 h2 h3;
  assert (Buffer.live h2 aad); //seem to need this hint
  assert (Buffer.live h3 aad); //seem to need this hint
  Buffer.lemma_reveal_modifies_0 h2 h3;
  MAC.mac ak l acc tag;
  let h4 = get () in
  FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 tag h3) h4;
  modifies_fresh_empty i n st.prf.mac_rgn ak h0 h3 h4;
  assert (safeId i ==> HS.modifies_ref st.prf.mac_rgn TSet.empty h0 h4);
  frame_pre_refines i st n (v plainlen) plain cipher_tagged h0 h3 h4;
  intro_mac_refines i st n aad plain cipher_tagged h4;
  pre_refines_to_refines i st n aadlen aad (v plainlen) plain cipher_tagged h0 h4;
  extend_refines_aux i st n aadlen aad (v plainlen) plain cipher_tagged h0 h4;
  admit()


  
  (* let _ = *)
  (*   let tab = HS.sel h4 (itable i st.prf) in *)
  (*   match PRF.find_mac tab x with *)
  (*   | None -> assert False *)
  (*   | Some mac_st -> assert(mac_st == ak) in *)
  (* admit() *)
  

  (* admit() *)

    
      (*  admit() in *)
       
      (* let c = Buffer.as_seq h4 cipher in *)
      (* let ad = Buffer.as_seq h4 aad in *)
      (* assume (l == field_encode i ad #plainlen c); *)
      (* intro_mac_refines i st n aad plain cipher_tagged h4 in *)

  (*   () in  *)
  (* admit() *)
  


  (* assume (mac_refines i st.prf.mac_rgn (v plainlen) (as_seq h4 aad) (Plain.sel_plain h4 plainLen plain) (Buffer.as_seq tag) _ h4); *)
  (* assume false *)

  
  (* let h4 = get () in  *)
  (* assume (HS (modifies (Set.union (Set.singleton (Buffer.frameOf tag)) *)
  (* 				  (Set.singleton st.prf.mac_rgn)) h3 h4)); *)
  (* assume (Buffer.modifies_buf_1 (Buffer.frameOf tag) tag h3 h4); *)
  (* let _ =  *)
  (*   let mod_set = MAC (if mac_log then !{HS.as_ref (as_hsref (MAC.ilog ak.log))} else !{}) in *)
  (*   assume (HS (modifies_ref st.prf.mac_rgn mod_set h3 h4)) in *)
  (* if safeId i *)
  (* then begin *)
  (*   let aad = temp_to_seq aad in *)
  (*   let p = temp_get_plain plain in *)
  (*   let c = temp_to_seq cipher in *)
  (*   assume false; *)
  (*   let entry = Entry n aad (v plainlen) p c in *)
  (*   st.log := SeqProperties.snoc !st.log entry *)
  (* end; *)
  (* assume false *)
  (* pop_frame() *)
