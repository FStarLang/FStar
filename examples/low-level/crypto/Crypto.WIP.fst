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
  
#reset-options "--z3timeout 400 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

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
     extend_refines h0 i mac_rgn entries_0 blocks_0 entry blocks_1 h1

assume val to_seq_temp: #a:Type -> b:Buffer.buffer a -> l:UInt32.t{v l <= Buffer.length b} -> ST (Seq.seq a)
  (requires (fun h -> Buffer.live h b))
  (ensures  (fun h0 r h1 -> h0 == h1 /\ Buffer.live h1 b /\ r == Buffer.as_seq h1 b))

#reset-options "--z3timeout 400 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let rec frame_refines (i:id{safeId i}) (mac_rgn:region) 
		      (entries:Seq.seq (entry i)) (blocks:Seq.seq (PRF.entry mac_rgn i))
		      (h:mem) (h':mem)
   : Lemma (requires refines h i mac_rgn entries blocks /\
		     HS.modifies_ref mac_rgn TSet.empty h h' /\
		     HS.live_region h' mac_rgn)
	   (ensures  refines h' i mac_rgn entries blocks)
	   (decreases (Seq.length entries))
   = if Seq.length entries = 0 then 
       ()
     else let e = SeqProperties.head entries in
          let b = num_blocks e in 
         (let blocks_for_e = Seq.slice blocks 0 (b + 1) in
       	  let entries_tl = SeqProperties.tail entries in
          let blocks_tl = Seq.slice blocks (b+1) (Seq.length blocks) in
	  frame_refines i mac_rgn entries_tl blocks_tl h h';
	  frame_refines_one_entry h i mac_rgn e blocks_for_e h')

#reset-options "--z3timeout 400 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
val refines_to_inv: (i:id) -> (st:state i Writer) -> (nonce:Cipher.iv (alg i)) ->
		       (aadlen: UInt32.t {aadlen <=^ aadmax}) ->
		       (aad: lbuffer (v aadlen)) ->
		       (len: UInt32.t {len <> 0ul}) ->
		       (plain:plainBuffer i (v len)) -> 
		       (cipher:lbuffer (v len + v (Spec.taglen i))) ->
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
			~ (st.log === (itable i st.prf)) /\
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

let my_inv (#i:id) (#rw:_) (st:state i rw) (h:mem) = 
  inv h st /\
  HS (h.h `Map.contains` st.prf.mac_rgn) /\
  (safeId i ==> h `HS.contains` st.log) /\
  (prf i ==> (h `HS.contains` (itable i st.prf) /\
	     ~ (st.log === (itable i st.prf))))

let mac_ensures (i:MAC.id) (st:MAC.state i) (l:MAC.itext) (acc:MAC.accB i) (tag:MAC.tagB) 
		(h0:mem) (h1:mem) = 
    let open FStar.Buffer in
    let open Crypto.Symmetric.Bytes in
    let open Crypto.Symmetric.Poly1305 in
    let open Crypto.Symmetric.Poly1305.Spec in
    let open Crypto.Symmetric.Poly1305.MAC in
    live h0 st.s /\ 
    live h0 st.r /\ 
    live h1 tag /\ (
    if mac_log then
      HS.modifies (as_set [st.region; Buffer.frameOf tag]) h0 h1 /\
      mods_2 [HS.Ref (as_hsref (ilog st.log)); HS.Ref (Buffer.content tag)] h0 h1 /\
      Buffer.modifies_buf_1 (Buffer.frameOf tag) tag h0 h1 /\
      HS.modifies_ref st.region !{HS.as_ref (as_hsref (ilog st.log))} h0 h1 /\
      m_contains (ilog st.log) h1 /\ (
      let mac = mac_1305 l (sel_elem h0 st.r) (sel_word h0 st.s) in
      mac == little_endian (sel_word h1 tag) /\
      m_sel h1 (ilog st.log) == Some (l, sel_word h1 tag))
    else Buffer.modifies_1 tag h0 h1)

let encrypt_ensures (i:id) (st:state i Writer)
		    (n: Cipher.iv (alg i))
		    (aadlen: UInt32.t {aadlen <=^ aadmax})
		    (aad: lbuffer (v aadlen))
		    (plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) 1ul})
		    (plain: plainBuffer i (v plainlen))
		    (cipher_tagged:lbuffer (v plainlen + v (Spec.taglen i)))
		    (h0:mem) (h5:mem) = 
     Buffer.live h5 aad /\
     Buffer.live h5 cipher_tagged /\
     Plain.live h5 plain /\
     my_inv st h5 /\
     HS.modifies_transitively (as_set [st.log_region; Buffer.frameOf cipher_tagged]) h0 h5 /\ (
     safeId i ==>  (
       let aad = Buffer.as_seq h5 aad in
       let p = Plain.sel_plain h5 plainlen plain in
       let c = Buffer.as_seq h5 cipher_tagged in
       HS.sel h5 st.log == SeqProperties.snoc (HS.sel h0 st.log) (Entry n aad (v plainlen) p c)))

val finish_after_mac: h0:mem -> h3:mem -> i:id -> st:state i Writer -> 
		      n: Cipher.iv (alg i) ->
		      aadlen: UInt32.t {aadlen <=^ aadmax} -> 
		      aad: lbuffer (v aadlen) -> 
		      plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) 1ul} -> 
		      plain: plainBuffer i (v plainlen) -> 
		      cipher_tagged:lbuffer (v plainlen + v (Spec.taglen i)) ->
		      ak:MAC.state (i, n) -> l:MAC.itext -> acc:MAC.accB (i, n) -> tag:MAC.tagB -> ST unit 
  (requires (fun h4 -> 
    let cipher = Buffer.sub cipher_tagged 0ul plainlen in
    let x0 = {iv=n; ctr=0ul} in
    HS.modifies_transitively (as_set [st.log_region; Buffer.frameOf cipher_tagged]) h0 h3 /\
    HS.modifies_ref st.prf.mac_rgn TSet.empty h0 h3 /\
    pre_refines_one_entry i st n (v plainlen) plain cipher_tagged h0 h3 /\
    mac_ensures (i, n) ak l acc tag h3 h4 /\
    (my_inv st h0) /\
    (MAC (ak.region = st.prf.mac_rgn)) /\
    (safeId i ==> ~ (m_contains (MAC (ilog ak.log)) h0)) /\
    (prf i ==> HS.frameOf (PRF.itable i st.prf) <> Buffer.frameOf cipher_tagged) /\
    (Buffer.disjoint (Plain.as_buffer plain) cipher_tagged) /\
    (Buffer.disjoint aad cipher_tagged) /\
    (HH.disjoint (Buffer.frameOf (Plain.as_buffer plain)) st.log_region) /\
    (HH.disjoint (Buffer.frameOf cipher_tagged) st.log_region) /\  
    (Buffer.live h3 cipher_tagged) /\
    (Plain.live h3 plain) /\
    (Buffer.live h3 aad) /\
    (tag == Buffer.sub cipher_tagged plainlen (Spec.taglen i)) /\
    (mac_log ==> l == encode_both aadlen (Buffer.as_seq h3 aad) plainlen (Buffer.as_seq h3 cipher)) /\ //from accumulate
    (safeId i ==>
	HS.modifies_ref st.log_region (TSet.singleton (FStar.Heap.Ref (HS.as_ref (PRF.itable i st.prf)))) h0 h3 /\ (
	let tab = HS.sel h3 (PRF.itable i st.prf) in
	match PRF.find_mac tab x0 with
	| None -> False
	| Some mac_st -> mac_st == ak))))
   (ensures (fun _ _ h5 -> 
	      encrypt_ensures i st n aadlen aad plainlen plain cipher_tagged h0 h5))
let finish_after_mac h0 h3 i st n aadlen aad plainlen plain cipher_tagged ak l acc tag = 
  if prf i then recall (itable i st.prf);
  if safeId i then recall st.log;
  let h4 = get () in
  if safeId i 
  then begin
    intro_mac_refines i st n aad plain cipher_tagged h4;
    modifies_fresh_empty i n st.prf.mac_rgn ak h0 h3 h4;
    frame_pre_refines i st n (v plainlen) plain cipher_tagged h0 h3 h4;
    pre_refines_to_refines i st n aadlen aad (v plainlen) plain cipher_tagged h0 h4;
    extend_refines_aux i st n aadlen aad (v plainlen) plain cipher_tagged h0 h4;
    refines_to_inv i st n aadlen aad plainlen plain cipher_tagged
  end
  else FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 tag h3) h4
  
val encrypt:
  i: id -> st:state i Writer ->
  n: Cipher.iv (alg i) ->
  aadlen: UInt32.t {aadlen <=^ aadmax} ->
  aad: lbuffer (v aadlen) ->
  plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) 1ul} ->
  plain: plainBuffer i (v plainlen) ->
  cipher_tagged:lbuffer (v plainlen + v (Spec.taglen i))
  {
    Buffer.disjoint aad cipher_tagged /\
    Buffer.disjoint (Plain.as_buffer plain) aad /\
    Buffer.disjoint (Plain.as_buffer plain) cipher_tagged /\
    HH.disjoint (Buffer.frameOf (Plain.as_buffer plain)) st.log_region /\
    HH.disjoint (Buffer.frameOf cipher_tagged) st.log_region /\
    HH.disjoint (Buffer.frameOf aad) st.log_region
  }
  ->
  //STL -- should be STL eventually, but this requires propagation throughout the library
  ST unit
  (requires (fun h ->
    let prf_rgn = st.prf.rgn in
    my_inv st h /\
    Buffer.live h aad /\
    Buffer.live h cipher_tagged /\
    Plain.live h plain /\
    (prf i ==> none_above ({iv=n; ctr=0ul}) st.prf h) // The nonce must be fresh!
   ))
  (ensures (fun h0 _ h5 ->
    encrypt_ensures i st n aadlen aad plainlen plain cipher_tagged h0 h5))
    (* Buffer.m_ref (Buffer.frameOf cipher) !{Buffer.modifies_1 cipher h0 h1 /\  *) 
unfold let mac_ensures_2 (i:MAC.id) (st:MAC.state i) (l:MAC.itext) (acc:MAC.accB i) (tag:MAC.tagB) 
		(h0:mem) (h1:mem) = 
    let open FStar.Buffer in
    let open Crypto.Symmetric.Bytes in
    let open Crypto.Symmetric.Poly1305 in
    let open Crypto.Symmetric.Poly1305.Spec in
    let open Crypto.Symmetric.Poly1305.MAC in
    live h0 st.s /\ 
    live h0 st.r /\ 
    live h1 tag /\ (
    if mac_log then
      HS.modifies (as_set [st.region; Buffer.frameOf tag]) h0 h1 /\
      mods_2 [HS.Ref (as_hsref (ilog st.log)); HS.Ref (Buffer.content tag)] h0 h1 /\
      Buffer.modifies_buf_1 (Buffer.frameOf tag) tag h0 h1 /\
      HS.modifies_ref st.region !{HS.as_ref (as_hsref (ilog st.log))} h0 h1 /\
      m_contains (ilog st.log) h1 /\ (
      let mac = mac_1305 l (sel_elem h0 st.r) (sel_word h0 st.s) in
      mac == little_endian (sel_word h1 tag) /\
      m_sel h1 (ilog st.log) == Some (l, sel_word h1 tag))
    else Buffer.modifies_1 tag h0 h1)
    
let mac_wrapper (#i:MAC.id) (st:MAC.state i) (l:MAC.itext) (acc:MAC.accB i) (tag:MAC.tagB)
  : ST unit
    (requires (fun h0 ->
      let open Crypto.Symmetric.Poly1305.MAC in
      Buffer.live h0 tag /\ 
      Buffer.live h0 st.s /\
      Buffer.disjoint acc st.s /\ 
      Buffer.disjoint tag acc /\ 
      Buffer.disjoint tag st.r /\ 
      Buffer.disjoint tag st.s /\
      MAC.acc_inv st l acc h0 /\
      (MAC (mac_log ==> m_contains (ilog st.log) h0)) /\
      (MAC (mac_log /\ safeId (fst i) ==> m_sel h0 (ilog st.log) == None))))
  (ensures (fun h0 _ h1 -> mac_ensures i st l acc tag h0 h1))
 = let h0 = get () in
   MAC.mac #i st l acc tag;
   let h1 = get () in
   assume (HS.modifies (as_set [MAC st.region; Buffer.frameOf tag]) h0 h1);
   admit()
   
#reset-options "--z3timeout 1000 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let encrypt i st n aadlen aad plainlen plain cipher_tagged =
  let h0 = get() in
  assume (HS (is_stack_region h0.tip)); //TODO: remove this once we move all functions to STL
  assume (HS (HH.disjoint h0.tip st.prf.mac_rgn)); //DO we need disjointness or will disequality do?
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
  //Establishing the pre-conditions of MAC.mac
  let h3 = get() in
  assume (HS.modifies_transitively (as_set [st.log_region; Buffer.frameOf cipher_tagged]) h0 h3); //TODO: prove this!
  Buffer.lemma_reveal_modifies_0 h2 h3;
  assert (HS.modifies_ref st.prf.mac_rgn TSet.empty h0 h3);
  frame_pre_refines_0 i st n (v plainlen) plain cipher_tagged h0 h2 h3;
  assert (Buffer.live h2 aad); //seem to need this hint
  assert (Buffer.live h3 aad); //seem to need this hint
  Buffer.lemma_reveal_modifies_0 h2 h3;
  //MAC
  mac_wrapper #(i,n) ak l acc tag;
  //Some ideal and proof steps, to finish up
  finish_after_mac h0 h3 i st n aadlen aad plainlen plain cipher_tagged ak l acc tag;
  let h5 = get () in
  assume (HS.equal_domains h0 h5)

