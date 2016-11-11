module Crypto.AEAD

// Implements agile, conditionally secure Authenticated Encryption
// with Associated Data (AEAD) for TLS 1.2 and 1.3, given secure, 
// agile PRF cipher and UF-1CMA MAC. 

// For the security proof, we maintain a stateful invariant that
// precisely relates the contents of the AEAD log to the states of the
// PRF and the MACs.

// This file intends to match the spec of AEAD0.fst in mitls-fstar. 

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
open Crypto.AEAD.Lemmas
open Crypto.AEAD.Lemmas.Part2
open Crypto.AEAD.Lemmas.Part3
open Crypto.AEAD.Wrappers

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module MAC = Crypto.Symmetric.MAC
module CMA = Crypto.Symmetric.UF1CMA

module Plain = Crypto.Plain
module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF

type region = rgn:HH.rid {HS.is_eternal_region rgn}

let ctr x = PRF(x.ctr)

// Overview of the stateful invariant:
//
// We allocate AEAD logs at the writer (complying with our `local modifier' discipline)
// We allocate all PRF tables in a global private region (to escape that discipline)

// Global state invariant: 
// for all ideal instances of AEAD, 
// - their regions and PRFs tables are pairwise disjoint; and
// - their PRF table contents correctly refines their AEAD logs,
//     (up to early decryptor allocations in initial state)

// This invariant depends only on AEAD-writer regions and the PRF region. 
//
// During AE encrypt, the invariant is eventually restored as we extend the AEAD log, 
// using a precise record of all entries added to the PRF table during encryption.
//
// During AE decrypt, the only interesting case is when early
// verification fails: the invariant is restored for an extended PRF
// state with an extra MAC in its initial state.
//
// For convenience, 'refines' relies on both the log and the table being ordered chronologically.

// TODO `Functional' correctness? (actually a witnessed, stable property)
// c = encryptT h i st nonce ad (real_or_zero i p) 
//
// Ideally, this depends on the (increasing) states of 
// both the PRF and its MACs, and may follow from the global invariant.
//
// Really, this depends on the functional correctness of PRF. 
// Needed: prf_read returning a ghost of the actual underlying block. 
//let sub s start len = Seq.slice start (start+len) s // more convenient? 

val gen: i:id -> rgn:region -> ST (state i Writer)
  (requires (fun _ -> True))
  (ensures  (fun h0 st h1 -> True))
let gen i rgn = 
  let prf = PRF.gen rgn i in 
  if Flag.prf i then recall (PRF.itable i prf);
  let log = ralloc rgn (Seq.createEmpty #(entry i)) in
  let ak = if CMA.skeyed i then Some (PRF.prf_sk0 #i prf) else None in 
  State #i #Writer #rgn log prf ak

val coerce: i:id{~(prf i)} -> rgn:region -> key:lbuffer (v (PRF.keylen i)) -> ST (state i Writer)
  (requires (fun h -> Buffer.live h key))
  (ensures  (fun h0 st h1 -> True))
let coerce i rgn key = 
  let prf = PRF.coerce rgn i key in
  if Flag.prf i then recall (PRF.itable i prf);
  let log = ralloc rgn (Seq.createEmpty #(entry i)) in // Shouldn't exist
  let ak = if CMA.skeyed i then Some (PRF.prf_sk0 #i prf) else None in 
  State #i #Writer #rgn log prf ak

val genReader: #i:id -> st:state i Writer -> ST (state i Reader)
  (requires (fun _ -> True))
  (ensures  (fun _ _ _ -> True))
let genReader #i st =
  State #i #Reader #st.log_region st.log st.prf st.ak

val leak: #i:id{~(prf i)} -> st:state i Writer -> ST (lbuffer (v (PRF.statelen i)))
  (requires (fun _ -> True))
  (ensures  (fun _ _ _ -> True))
let leak #i st = PRF.leak st.prf

(* notes 16-10-04 

Not sure what's the best style to push as an invariant.
It may be easier to first split blocks by iv. 

This corresponds to the PRF state "at rest" for the invariant.
Should be uniform between i:id {MAC.ideal /\ authId i }.

For the dexor loop, we have as `pre` that the PRF state contains the correct entries.
We need as a monotonic invariant that "containing implies finding"; more like map than seq.

For the enxor loop, we need a finer, transient invariant for the last chunk of the PRF log. 

*) 

// COUNTER_MODE LOOP from Chacha20 

// XOR-based encryption and decryption (just swap ciphertext and plaintext)
// prf i    ==> writing at most at indexes x and above (same iv, higher ctr) at the end of the PRF table.
// safeId i ==> appending *exactly* "counterblocks i x l plain cipher" at the end of the PRF table
//              the proof seems easier without tail recursion.

val counter_enxor: 
  i:id -> t:PRF.state i -> x:PRF.domain i{PRF.ctr_0 i <^ x.ctr} ->
  len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)} ->
  remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len} ->
  plain:plainBuffer i (v len) ->
  cipher:lbuffer (v len)
  { let bp = as_buffer plain in 
    Buffer.disjoint bp cipher /\
    Buffer.frameOf bp <> (PRF t.rgn) /\
    Buffer.frameOf cipher <> (PRF t.rgn) 
  } -> 
  h_init:mem ->
  // Not Stack, as we modify the heap-based ideal table (and don't know where the buffers are
  ST unit
  (requires (fun h -> 
    let initial_domain = {x with ctr=ctr_0 i +^ 1ul} in
    let completed_len = len -^ remaining_len in 
    Plain.live h plain /\ 
    Buffer.live h cipher /\ 
    (remaining_len <> 0ul ==> FStar.Mul ((v x.ctr - v (offset i)) * v (PRF.blocklen i) = v completed_len)) /\
    // if ciphertexts are authenticated, then fresh blocks are available
    none_above x t h /\
    (safeId i
      ==> (let r = itable i t in 
	   h `HS.contains` r /\
	   Seq.equal (HS.sel h t.table)
    		     (Seq.append (HS.sel h_init t.table)
    				 (counterblocks i t.mac_rgn initial_domain
    				      (v len) 0 (v completed_len)
    				      (Plain.sel_plain h len plain)
    				      (Buffer.as_seq h cipher)))))
    ))
  (ensures (fun h0 _ h1 -> 
    let initial_domain = {x with ctr=ctr_0 i +^ 1ul} in
    Plain.live h1 plain /\
    Buffer.live h1 cipher /\
    // in all cases, we extend the table only at x and its successors.
    modifies_table_above_x_and_buffer t x cipher h0 h1 /\
    (safeId i
      ==> HS.sel h1 t.table ==
    	  Seq.append (HS.sel h_init t.table)
    		     (counterblocks i t.mac_rgn initial_domain
    				      (v len) 0 (v len)
    				      (Plain.sel_plain h1 len plain)
    				      (Buffer.as_seq h1 cipher)))
    ))
#set-options "--z3timeout 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let rec counter_enxor i t x len remaining_len plain cipher h_init =
  let completed_len = len -^ remaining_len in
  let h0 = get () in
  if safeId i then ST.recall (itable i t);
  if remaining_len <> 0ul then
    begin // at least one more block
      let starting_pos = len -^ remaining_len in
      let l = min remaining_len (PRF.blocklen i) in
      let cipher_hd = Buffer.sub cipher starting_pos l in 
      let plain_hd = Plain.sub plain starting_pos l in 
      PRF.prf_enxor i t x l cipher_hd plain_hd;
      let h1 = get () in 
      x_buffer_1_modifies_table_above_x_and_buffer t x cipher h0 h1;
      prf_enxor_leaves_none_strictly_above_x t x len remaining_len cipher h0 h1;
      extending_counter_blocks t x (v len) (v completed_len) plain cipher h0 h1 h_init;
      let y = PRF.incr i x in
      counter_enxor i t y len (remaining_len -^ l) plain cipher h_init;
      let h2 = get () in
      trans_modifies_table_above_x_and_buffer t x y cipher h0 h1 h2
    end
  else refl_modifies_table_above_x_and_buffer t x cipher h0

let prf_state (#i:id) (#rw:rw) (e:state i rw) : PRF.state i = State.prf e
////////////////////////////////////////////////////////////////////////////////

#reset-options "--z3timeout 400 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
val extend_refines_aux: (i:id) -> (st:state i Writer) -> (nonce:Cipher.iv (alg i)) ->
		       (aadlen: UInt32.t {aadlen <=^ aadmax}) ->
		       (aad: lbuffer (v aadlen)) ->
                       (len:nat{len<>0}) -> (plain:plainBuffer i len) -> (cipher:lbuffer (len + v MAC.taglen)) ->
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

#reset-options "--z3timeout 400 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let encrypt_ensures' (regions:Set.set HH.rid)
		     (i:id) (st:state i Writer)
		     (n: Cipher.iv (alg i))
 		     (aadlen: UInt32.t {aadlen <=^ aadmax})
		     (aad: lbuffer (v aadlen))
		     (plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (ctr_0 i +^ 1ul)})
		     (plain: plainBuffer i (v plainlen))
		     (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
		     (h0:mem) (h5:mem) = 
     Buffer.live h5 aad /\
     Buffer.live h5 cipher_tagged /\
     Plain.live h5 plain /\
     my_inv st h5 /\
     HS.modifies_transitively regions h0 h5 /\ (
     safeId i ==>  (
       let aad = Buffer.as_seq h5 aad in
       let p = Plain.sel_plain h5 plainlen plain in
       let c = Buffer.as_seq h5 cipher_tagged in
       HS.sel h5 st.log == SeqProperties.snoc (HS.sel h0 st.log) (Entry n aad (v plainlen) p c)))

let encrypt_ensures_tip (i:id) (st:state i Writer)
		     (n: Cipher.iv (alg i))
 		     (aadlen: UInt32.t {aadlen <=^ aadmax})
		     (aad: lbuffer (v aadlen))
		     (plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (ctr_0 i +^ 1ul)})
		     (plain: plainBuffer i (v plainlen))
		     (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
		     (h0:mem) (h5:mem) =
  encrypt_ensures' (Set.as_set [st.log_region; Buffer.frameOf cipher_tagged; HS h5.tip])
    i st n aadlen aad plainlen plain cipher_tagged h0 h5

let encrypt_ensures  (i:id) (st:state i Writer)
		     (n: Cipher.iv (alg i))
 		     (aadlen: UInt32.t {aadlen <=^ aadmax})
		     (aad: lbuffer (v aadlen))
		     (plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (ctr_0 i +^ 1ul)})
		     (plain: plainBuffer i (v plainlen))
		     (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
		     (h0:mem) (h5:mem) =
  encrypt_ensures' (Set.as_set [st.log_region; Buffer.frameOf cipher_tagged])
    i st n aadlen aad plainlen plain cipher_tagged h0 h5

val finish_after_mac: h0:mem -> h3:mem -> i:id -> st:state i Writer -> 
		      n: Cipher.iv (alg i) ->
		      aadlen: UInt32.t {aadlen <=^ aadmax} -> 
		      aad: lbuffer (v aadlen) -> 
		      plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (ctr_0 i +^ 1ul)} -> 
		      plain: plainBuffer i (v plainlen) -> 
		      cipher_tagged:lbuffer (v plainlen + v MAC.taglen) ->
		      ak:CMA.state (i, n) -> acc:CMA.accBuffer (i, n) -> tag:MAC.tagB -> ST unit
  (requires (fun h4 -> 
    let cipher = Buffer.sub cipher_tagged 0ul plainlen in
    let x0 = {iv=n; ctr=ctr_0 i} in
    HS (h0.tip = h4.tip) /\
    HH.disjoint (HS h4.tip) st.log_region /\
    HH.disjoint (HS h4.tip) (Buffer.frameOf cipher_tagged) /\
    HS.modifies_transitively (Set.as_set [st.log_region; Buffer.frameOf cipher_tagged; HS h4.tip]) h0 h3 /\
    HS.modifies_ref st.prf.mac_rgn TSet.empty h0 h3 /\
    (prf i ==> none_above ({iv=n; ctr=ctr_0 i}) st.prf h0) /\ // The nonce must be fresh!
    pre_refines_one_entry i st n (v plainlen) plain cipher_tagged h0 h3 /\
    mac_ensures (i, n) ak acc tag h3 h4 /\
    (my_inv st h0) /\
    (CMA (ak.region = st.prf.mac_rgn)) /\
    (safeId i ==> ~ (m_contains (CMA (ilog ak.log)) h0)) /\
    (prf i ==> HS.frameOf (PRF.itable i st.prf) <> Buffer.frameOf cipher_tagged) /\
    (Buffer.disjoint (Plain.as_buffer plain) cipher_tagged) /\
    (Buffer.disjoint aad cipher_tagged) /\
    (HH.disjoint (Buffer.frameOf (Plain.as_buffer plain)) st.log_region) /\
    (HH.disjoint (Buffer.frameOf cipher_tagged) st.log_region) /\  
    (Buffer.live h3 cipher_tagged) /\
    (Plain.live h3 plain) /\
    (Buffer.live h3 aad) /\
    (tag == Buffer.sub cipher_tagged plainlen MAC.taglen) /\
    (mac_log ==> 
      (h3 `HS.contains` CMA.alog acc) /\
      (HS.frameOf (CMA.alog acc) = HS h3.tip) /\
      FStar.HyperStack.sel h3 (CMA.alog acc) ==
      encode_both i aadlen (Buffer.as_seq h3 aad) plainlen (Buffer.as_seq h3 cipher)) /\ //from accumulate
    (safeId i ==>
	HS.modifies_ref st.log_region (TSet.singleton (FStar.Heap.Ref (HS.as_ref (PRF.itable i st.prf)))) h0 h3 /\ (
	let tab = HS.sel h3 (PRF.itable i st.prf) in
	match PRF.find_mac tab x0 with
	| None -> False
	| Some mac_st -> mac_st == ak))))
   (ensures (fun _ _ h5 -> 
              encrypt_ensures_tip i st n aadlen aad plainlen plain cipher_tagged h0 h5))

#reset-options "--z3timeout 1000 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let finish_after_mac h0 h3 i st n aadlen aad plainlen plain cipher_tagged ak acc tag = 
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

let encrypt_ensures_push_pop (i:id) (st:state i Writer)
		    (n: Cipher.iv (alg i))
		    (aadlen: UInt32.t {aadlen <=^ aadmax})
		    (aad: lbuffer (v aadlen))
		    (plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (ctr_0 i +^ 1ul)})
		    (plain: plainBuffer i (v plainlen))
		    (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
		    (h:mem) (h0:mem) (h5:mem)
   : Lemma (requires (let open FStar.HyperStack in
		      fresh_frame h h0 /\
		      HH.disjoint st.log_region h0.tip /\
		      HH.disjoint (Buffer.frameOf (Plain.as_buffer plain)) h0.tip /\
     		      HH.disjoint (Buffer.frameOf aad) h0.tip /\
      		      HH.disjoint (Buffer.frameOf cipher_tagged) h0.tip /\
		      encrypt_ensures_tip i st n aadlen aad plainlen plain cipher_tagged h0 h5))
	   (ensures (HS.poppable h5 /\
		     encrypt_ensures i st n aadlen aad plainlen plain cipher_tagged h (HS.pop h5)))
   = if safeId i
     then frame_refines i st.prf.mac_rgn (HS.sel h5 st.log) (HS.sel h5 (PRF.itable i st.prf)) h5 (HS.pop h5)
     

val encrypt:
  i: id -> st:state i Writer ->
  n: Cipher.iv (alg i) ->
  aadlen: UInt32.t {aadlen <=^ aadmax} ->
  aad: lbuffer (v aadlen) ->
  plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (ctr_0 i +^ 1ul)} ->
  plain: plainBuffer i (v plainlen) ->
  cipher_tagged:lbuffer (v plainlen + v MAC.taglen)
  {
    Buffer.disjoint aad cipher_tagged /\
    Buffer.disjoint (Plain.as_buffer plain) aad /\
    Buffer.disjoint (Plain.as_buffer plain) cipher_tagged /\
    HH.disjoint (Buffer.frameOf (Plain.as_buffer plain)) st.log_region /\
    HH.disjoint (Buffer.frameOf cipher_tagged) st.log_region /\
    HH.disjoint (Buffer.frameOf aad) st.log_region /\
    HS.is_eternal_region st.log_region /\
    HS.is_eternal_region (Buffer.frameOf cipher_tagged) /\
    HS.is_eternal_region (Buffer.frameOf (Plain.as_buffer plain)) /\
    HS.is_eternal_region (Buffer.frameOf aad) /\
    st.log_region <> HH.root /\
    Buffer.frameOf cipher_tagged <> HH.root /\
    Buffer.frameOf aad <> HH.root /\
    Buffer.frameOf (Plain.as_buffer plain) <> HH.root
  }
  ->
  //
  ST unit
  (requires (fun h ->
    let prf_rgn = st.prf.rgn in
    my_inv st h /\
    Buffer.live h aad /\
    Buffer.live h cipher_tagged /\
    Plain.live h plain /\
    st.log_region  `HS.is_in` (HS h.h) /\
    (prf i ==> none_above ({iv=n; ctr=ctr_0 i}) st.prf h) // The nonce must be fresh!
   ))
  (ensures (fun h0 _ h5 ->
    encrypt_ensures i st n aadlen aad plainlen plain cipher_tagged h0 h5))
let encrypt i st n aadlen aad plainlen plain cipher_tagged =
  let h_init = get() in
  push_frame();
  let h0 = get () in
  frame_myinv_push st h_init h0;
  assert (HH.modifies_rref st.prf.mac_rgn TSet.empty (HS h_init.h) (HS h0.h));
  assert (HS (is_stack_region h0.tip));
  assert (HS (HH.disjoint h0.tip st.log_region));
  assert (HS (HH.disjoint h0.tip (Buffer.frameOf cipher_tagged)));
  let x = PRF({iv = n; ctr = ctr_0 i}) in // PRF index to the first block
  let ak = PRF.prf_mac i st.prf st.ak x in  // used for keying the one-time MAC
  let h1 = get () in
  (* *)
  (* *)
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in
  let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in
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
  let acc = accumulate_wrapper ak aadlen aad plainlen cipher in
  //Establishing the pre-conditions of MAC.mac
  let h3 = get() in
  Buffer.lemma_reveal_modifies_0 h2 h3;
  assert (HS.modifies_transitively (Set.as_set [st.log_region; Buffer.frameOf cipher_tagged; HS h3.tip]) h0 h3);
  assert (HS.modifies_ref st.prf.mac_rgn TSet.empty h0 h3);
  frame_pre_refines_0 i st n (v plainlen) plain cipher_tagged h0 h2 h3;
  assert (Buffer.live h2 aad); //seem to need this hint
  assert (Buffer.live h3 aad); //seem to need this hint
  Buffer.lemma_reveal_modifies_0 h2 h3;
  //MAC
  mac_wrapper #(i,n) ak acc tag;
  //Some ideal and proof steps, to finish up
  finish_after_mac h0 h3 i st n aadlen aad plainlen plain cipher_tagged ak acc tag;
  let h5 = get () in
  pop_frame();
  encrypt_ensures_push_pop i st n aadlen aad plainlen plain cipher_tagged h_init h0 h5

////////////////////////////////////////////////////////////////////////////////
//DECRYPT SIDE
////////////////////////////////////////////////////////////////////////////////

//counter_dexor
let maybe_plain (i:id) (l:nat) = if safeId i then Plain.plain i l else unit
let as_plain (#i:id) (#l:nat) (m:maybe_plain i l{safeId i}) : plain i l = m

let decrypted_up_to (#i:id) (#len:u32) (completed:u32{completed <=^ len}) 
		    (pb:plainBuffer i (v len)) (p:maybe_plain i (v len)) 
		    (h:mem{Buffer.live h (as_buffer pb)}) =
  safeId i ==> 		    
    Seq.equal (as_bytes (Plain.slice (Plain.sel_plain h len pb) 0 (v completed)))
	      (as_bytes (Plain.slice (as_plain p) 0 (v completed)))

let decrypted_up_to_end (#i:id) (#len:u32) (pb:plainBuffer i (v len)) (p:maybe_plain i (v len)) 
			(h:mem{Buffer.live h (as_buffer pb)})
    : Lemma (requires (decrypted_up_to len pb p h))
	    (ensures (safeId i ==> Plain.sel_plain h len pb == as_plain p))
    = if safeId i then begin
	assert (Seq.equal (Plain.as_bytes (Plain.sel_plain h len pb))
			(Plain.as_bytes (Plain.slice (Plain.sel_plain h len pb) 0 (v len))));
        assert (Seq.equal (Plain.as_bytes (as_plain p))
	   		  (Plain.as_bytes (Plain.slice (as_plain p) 0 (v len))))
      end

let dexor_modifies (#i:id) (#len:u32) (t:PRF.state i) (x:PRF.domain i) 
		   (pb:plainBuffer i (v len)) (h0:mem) (h1:mem) =
   if not (prf i) || safeId i
   then Buffer.modifies_1 (as_buffer pb) h0 h1
   else modifies_table_above_x_and_buffer t x (as_buffer pb) h0 h1

#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let dexor_of_prf_dexor_modifies (#i:id) (#len:u32) (t:PRF.state i) 
				(x:PRF.domain i{ctr_0 i <^ x.ctr}) 
				(pb:plainBuffer i (v len)) (h0:mem) (h1:mem)
   : Lemma (requires (prf_dexor_modifies t x pb h0 h1))
	   (ensures (dexor_modifies t x pb h0 h1))
   = if not (prf i) || safeId i
     then ()
     else x_buffer_1_modifies_table_above_x_and_buffer t x (as_buffer pb) h0 h1

let dexor_modifies_trans (#i:id) (#len:u32) (t:PRF.state i) 
			 (x:PRF.domain i{ctr_0 i <^ x.ctr}) 
			 (y:PRF.domain i{y `above` x})
			 (pb:plainBuffer i (v len)) (h0:mem) (h1:mem) (h2:mem)
   : Lemma (requires (dexor_modifies t x pb h0 h1 /\
		      dexor_modifies t y pb h1 h2))
	   (ensures (dexor_modifies t x pb h0 h2))
   = if not (prf i) || safeId i
     then ()
     else trans_modifies_table_above_x_and_buffer t x y (as_buffer pb) h0 h1 h2

let dexor_modifies_refl (#i:id) (#len:u32) (t:PRF.state i) 
			 (x:PRF.domain i{ctr_0 i <^ x.ctr}) 
			 (pb:plainBuffer i (v len)) (h0:mem)
   : Lemma (requires (Buffer.live h0 (as_buffer pb)))
	   (ensures (dexor_modifies t x pb h0 h0))
   = if not (prf i) || safeId i
     then ()
     else refl_modifies_table_above_x_and_buffer t x (as_buffer pb) h0

let dexor_modifies_widen (#i:id) (#len:u32) (t:PRF.state i) 
			 (x:PRF.domain i{ctr_0 i <^ x.ctr}) 
			 (pb:plainBuffer i (v len))
			 (from:u32{FStar.Buffer (v from + v (Plain.as_buffer pb).idx) < pow2 n})
			 (len:u32{FStar.Buffer (v len <= length (Plain.as_buffer pb) /\ v from + v len <= length (Plain.as_buffer pb))})
			 (h0:mem) (h1:mem)
   : Lemma (requires (Buffer.live h0 (Plain.as_buffer pb) /\ 
		      dexor_modifies t x (Plain.sub pb from len) h0 h1))
	   (ensures (dexor_modifies t x pb h0 h1))
   = if not (prf i) || safeId i
     then (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer (Plain.sub pb from len)) h0 h1;
           Buffer.lemma_intro_modifies_1 (Plain.as_buffer pb) h0 h1)
     else ()

let rec contains_all_blocks (#i:id) (#r:rid)
  		 	    (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr})
			    (len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)})
			    (remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len})
			    (plain:maybe_plain i (v len))
			    (cipher:lbytes (v len))
			    (blocks:prf_blocks r i)
				   : GTot Type0 (decreases (v remaining_len))
   = if not (safeId i) || remaining_len = 0ul then 
       True
     else let starting_pos = len -^ remaining_len in
	  let l = min remaining_len (PRF.blocklen i) in
	  let plain_hd = Plain.slice (as_plain plain) (v starting_pos) (v starting_pos + v l) in
	  let cipher_hd = Seq.slice cipher (v starting_pos) (v starting_pos + v l) in
	  contains_cipher_block (v l) x cipher_hd blocks /\
	  contains_plain_block x plain_hd blocks /\
	  contains_all_blocks (PRF.incr i x) len (remaining_len -^ l) plain cipher blocks

#reset-options "--z3timeout 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let counter_dexor_sep (#i:id) (#len:u32)
		      (t:PRF.state i) 
		      (plain:plainBuffer i (v len))
		      (cipher:lbuffer (v len)) = 
    let bp = as_buffer plain in		      
    Buffer.disjoint bp cipher /\
    Buffer.frameOf bp <> (PRF t.rgn) /\
    Buffer.frameOf cipher <> (PRF t.rgn)

let counter_dexor_live (#i:id) (#len:u32)
		       (t:PRF.state i) 
 		       (plain:plainBuffer i (v len))
		       (cipher:lbuffer (v len)) (h:mem) =
    Plain.live h plain /\
    Buffer.live h cipher /\
    (prf i ==> h `HS.contains` (itable i t))

let contains_all_blocks' (#i:id)
 		 	 (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr})
			 (len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)})
			 (remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len})
			 (plain:maybe_plain i (v len))
			 (cipher:lbuffer (v len))
			 (t:PRF.state i)
			 (h:mem)
   = safeId i /\ Buffer.live h cipher ==> 				
     contains_all_blocks x len remaining_len plain (Buffer.as_seq h cipher) (HS.sel h (PRF.itable i t))
     
let frame_contains_all_blocks (i:id) 
			      (x_init:PRF.domain i{PRF.ctr_0 i <^ x_init.ctr})
     			      (x:PRF.domain i{x `above` x_init})
			      (len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)})
			      (remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len})
			      (t:PRF.state i) 
			      (pb:plainBuffer i (v len))
			      (p:maybe_plain i (v len))
			      (cipher: lbuffer (v len))
			      (h0:mem)
    			      (h1:mem)
   : Lemma (requires (counter_dexor_sep t pb cipher  /\
		      counter_dexor_live t pb cipher h0 /\
		      contains_all_blocks' x len remaining_len p cipher t h0 /\
                      prf_dexor_modifies t x_init pb h0 h1))
          (ensures  (counter_dexor_live t pb cipher h1 /\
		     contains_all_blocks' x len remaining_len p cipher t h1))
   = FStar.Classical.move_requires (FStar.Buffer.lemma_reveal_modifies_1 (as_buffer pb) h0) h1

#reset-options "--z3timeout 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let invert_contains_all_blocks (i:id) 
				      (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr})
				      (len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)})
				      (remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <> 0ul /\ remaining_len <=^ len})
				      (t:PRF.state i) 
				      (p:maybe_plain i (v len))
 				      (cipher: lbuffer (v len))
				      (h:mem{Buffer.live h cipher})
   : Lemma (requires (contains_all_blocks' x len remaining_len p cipher t h))
 	   (ensures  (let starting_pos = len -^ remaining_len in
	              let l = min remaining_len (PRF.blocklen i) in
		      let cipher_hd = Buffer.sub cipher starting_pos l in 
		      safeId i ==> (
		       let plain_hd = Plain.slice (as_plain p) (v starting_pos) (v starting_pos + v l) in
		       let blocks = HS.sel h (PRF.itable i t) in
		       let c = Buffer.as_seq h cipher_hd in
		       PRF.contains_cipher_block (v l) x c blocks /\
       		       PRF.contains_plain_block x plain_hd blocks /\
		       contains_all_blocks' (PRF.incr i x) len (remaining_len -^ l) p cipher t h)))
   = ()


let counter_dexor_requires (i:id) (t:PRF.state i) (x:PRF.domain i)
			   (len:u32) (remaining_len:u32)
			   (plain:plainBuffer i (v len))
			   (cipher:lbuffer (v len))
			   (p:maybe_plain i (v len))
			   (h:mem) =
    remaining_len_ok x len remaining_len /\			   
    (let bp = as_buffer plain in
     let initial_domain = {x with ctr=ctr_0 i +^ 1ul} in
     let completed_len = len -^ remaining_len in 
     counter_dexor_sep t plain cipher /\
     counter_dexor_live t plain cipher h /\
     // if ciphertexts are authenticated, then the table already includes all we need
     contains_all_blocks' x len remaining_len p cipher t h /\
     (safeId i ==> decrypted_up_to completed_len plain p h))
       
let counter_dexor_ensures (i:id) (t:PRF.state i) (x:PRF.domain i)
			  (len:u32)
			  (plain:plainBuffer i (v len))
			  (cipher:lbuffer (v len))
			  (p:maybe_plain i (v len))
			  (h0:mem) (h1:mem) = 
    Plain.live h1 plain /\
    Buffer.live h1 cipher /\
    // in all cases, we extend the table only at x and its successors.
    dexor_modifies t x plain h0 h1 /\
    (safeId i ==> 
       decrypted_up_to len plain p h1 /\
       Seq.equal (HS.sel h0 (PRF.itable i t)) (HS.sel h1 (PRF.itable i t)))

val extend_decrypted_up_to: #i:id -> (t:PRF.state i) -> (x:PRF.domain i) ->
			    #len:u32 -> (remaining_len:u32{remaining_len_ok x len remaining_len}) ->
			   (pb:plainBuffer i (v len)) ->
			   (p:maybe_plain i (v len)) ->
   			   (cipher:lbuffer (v len)) ->
			   (h0:mem) ->
			   (h1:mem) ->
      Lemma (requires (let starting_pos = len -^ remaining_len in
		       let l = min remaining_len (PRF.blocklen i) in
		       let plain = Plain.sub pb starting_pos l in
		       counter_dexor_sep t pb cipher /\
		       counter_dexor_live t pb cipher h0 /\
		       remaining_len <> 0ul /\
		       Plain.live h1 pb /\
		       prf_dexor_modifies t x plain h0 h1 /\
	               contains_all_blocks' x len remaining_len p cipher t h0 /\
		       (safeId i ==> 
			   decrypted_up_to starting_pos pb p h0 /\
			   contains_plain_block x (sel_plain h1 l plain) (HS.sel h1 (PRF.itable i t)))))
	    (ensures (let starting_pos = len -^ remaining_len in
		      let l = min remaining_len (PRF.blocklen i) in
		      Plain.live h1 pb /\
		      (safeId i ==> 
			   decrypted_up_to (starting_pos +^ l) pb p h1)))
#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let extend_decrypted_up_to #i t x #len remaining_len pb p cipher h0 h1 = 
  let starting_pos = len -^ remaining_len in
  let l = min remaining_len (PRF.blocklen i) in
  let frame = Plain.sub pb 0ul starting_pos in
  let plain = Plain.sub pb starting_pos l in
  assert (Buffer.disjoint (Plain.as_buffer frame) (Plain.as_buffer plain));
  let next = starting_pos +^ l in
  if safeId i then begin
    Buffer.lemma_reveal_modifies_1 (as_buffer plain) h0 h1;
    let pb_contents_0 = as_bytes (Plain.slice (Plain.sel_plain h0 len pb) 0 (v starting_pos)) in
    let p_contents_0  = as_bytes (Plain.slice (as_plain p) 0 (v starting_pos)) in
    let pb_contents_1 = as_bytes (Plain.slice (Plain.sel_plain h1 len pb) 0 (v next)) in
    let plain_contents_1 = as_bytes (Plain.sel_plain h1 l plain) in
    let frame_pb_contents_1 = as_bytes (Plain.slice (Plain.sel_plain h1 len pb) 0 (v starting_pos)) in
    assert (Seq.equal pb_contents_0 frame_pb_contents_1);
    assert (Seq.equal pb_contents_1 (Seq.append p_contents_0 plain_contents_1));
    invert_contains_all_blocks i x len remaining_len t p cipher h0
  end

 
val counter_dexor:
  i:id -> t:PRF.state i -> x:PRF.domain i ->
  len:u32 -> remaining_len:u32 ->
  plain:plainBuffer i (v len) ->
  cipher:lbuffer (v len) ->
  p:maybe_plain i (v len) ->
  ST unit (requires (fun h -> counter_dexor_requires i t x len remaining_len plain cipher p h))
 	  (ensures (fun h0 _ h1 -> counter_dexor_ensures i t x len plain cipher p h0 h1))
#reset-options "--z3timeout 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let rec counter_dexor i t x len remaining_len plain cipher p =
  let completed_len = len -^ remaining_len in
  let h0 = get () in
  if safeId i then ST.recall (itable i t);
  if remaining_len <> 0ul then
    begin // at least one more block
      let starting_pos = len -^ remaining_len in
      let l = min remaining_len (PRF.blocklen i) in
      let cipher_hd = Buffer.sub cipher starting_pos l in 
      let plain_hd = Plain.sub plain starting_pos l in 

      invert_contains_all_blocks i x len remaining_len t p cipher h0;
      prf_dexor i t x l cipher_hd plain_hd;
      
      let h1 = get() in 
      let y = PRF.incr i x in
      frame_contains_all_blocks i x y len (remaining_len -^ l) t plain p cipher h0 h1;
      FStar.Classical.move_requires (FStar.Buffer.lemma_reveal_modifies_1 (as_buffer plain) h0) h1;
      extend_decrypted_up_to t x remaining_len plain p cipher h0 h1;
      incr_remaining_len_ok x len remaining_len;

      counter_dexor i t y len (remaining_len -^ l) plain cipher p;

      let h2 = get () in
      dexor_of_prf_dexor_modifies t x plain_hd h0 h1;
      dexor_modifies_widen t x plain starting_pos l h0 h1;
      dexor_modifies_trans t x y plain h0 h1 h2;
      FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer plain) h0) h1;
      FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer plain) h1) h2
    end
   else dexor_modifies_refl t x plain h0


////////////////////////////////////////////////////////////////////////////////
//decrypt
////////////////////////////////////////////////////////////////////////////////
let decrypt_modifies (#i:id) (#len:u32) (st:state i Reader) (pb:plainBuffer i (v len)) (h0:mem) (h1:mem) =
   Crypto.AEAD.BufferUtils.decrypt_modifies (safeId i) st.log_region (as_buffer pb) h0 h1

let found_entry (#i:id) (n:Cipher.iv (alg i)) (st:state i Reader)
		(#aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen)) 
	        (#plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)})
		(cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
		(q:maybe_plain i (v plainlen))
		(h:mem) =
    Buffer.live h cipher_tagged /\
    Buffer.live h aad /\
    safeId i ==> 		
    (let entries = HS.sel h st.log in 		
     match find_entry n entries with
     | None -> False
     | Some (Entry nonce ad l p c) ->
         nonce == n /\
	 ad == Buffer.as_seq h aad /\
	 l  == v plainlen /\
	 c  == Buffer.as_seq h cipher_tagged /\ 
	 p  == as_plain q )

let decrypt_ok (#i:id) (n:Cipher.iv (alg i)) (st:state i Reader) 
	       (#aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen))
	       (#plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)}) 
	       (plain:plainBuffer i (v plainlen))
	       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
	       (verified:bool) (h1:mem) = 
  Buffer.live h1 aad /\
  Buffer.live h1 cipher_tagged /\
  Plain.live h1 plain /\
  (safeId i /\ verified ==> 
   found_entry n st aad cipher_tagged (Plain.sel_plain h1 plainlen plain) h1)

let decrypt_requires_live (#i:id) (st:state i Reader) 
			  (#aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen))
 			  (#plainlen:UInt32.t) (plain:plainBuffer i (v plainlen))
 			  (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) (h:mem) =
    Buffer.live h aad /\
    Plain.live h plain /\
    Buffer.live h cipher_tagged /\
    st.log_region `HS.is_in` (HS h.h) /\
    (prf i ==> h `HS.contains` (PRF.itable i st.prf))
    
let decrypt_requires_sep (#i:id) (st:state i Reader) 
			 (#aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen))
			 (#plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)}) 
			 (plain:plainBuffer i (v plainlen))
			 (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) =
    Buffer.disjoint aad cipher_tagged /\
    Buffer.disjoint (Plain.as_buffer plain) aad /\
    Buffer.disjoint (Plain.as_buffer plain) cipher_tagged /\
    HH.disjoint (Buffer.frameOf (Plain.as_buffer plain)) st.log_region /\
    HH.disjoint (Buffer.frameOf cipher_tagged) st.log_region /\
    HH.disjoint (Buffer.frameOf aad) st.log_region /\
    HS.is_eternal_region st.log_region /\
    HS.is_eternal_region (Buffer.frameOf cipher_tagged) /\
    HS.is_eternal_region (Buffer.frameOf (Plain.as_buffer plain)) /\
    HS.is_eternal_region (Buffer.frameOf aad) /\
    st.log_region <> HH.root /\
    Buffer.frameOf cipher_tagged <> HH.root /\
    Buffer.frameOf aad <> HH.root /\
    Buffer.frameOf (Plain.as_buffer plain) <> HH.root

let decrypt_when_auth (i:id) (n:Cipher.iv (alg i)) (st:state i Reader) (h0:mem) = 
  let x0 = {iv=n; ctr=ctr_0 i} in
  CMA.authId (i, n) ==> is_Some (find_mac (HS.sel h0 (itable i st.prf)) x0)

let is_mac_for_iv (#i:id) (#n:Cipher.iv (alg i)) (st:state i Reader{safeId i}) (ak:CMA.state (i, n)) (h:mem) = 
  let x0 = {iv=n; ctr=ctr_0 i} in 
  match find_mac (HS.sel h (itable i st.prf)) x0 with 
  | Some mac -> ak == mac
  | _ -> False

val counterblocks_contains_all_blocks:   
  i:id{safeId i} ->
  rgn:region -> 
  x:PRF.domain i ->
  len:u32 ->
  remaining_len:u32{remaining_len_ok x len remaining_len} ->
  plain:Crypto.Plain.plain i (v len) ->
  cipher:lbytes (v len) ->
  Lemma (requires True)
        (ensures
	    (let x0 = {x with ctr=ctr_0 i +^ 1ul} in
	     let all_blocks = counterblocks i rgn x0 (v len) 0 (v len) plain cipher in
	     let n_blocks = v x.ctr - v x0.ctr in
	     n_blocks <= Seq.length all_blocks /\
	     (let remaining_blocks = Seq.slice all_blocks n_blocks (Seq.length all_blocks) in
	      contains_all_blocks x len remaining_len plain cipher remaining_blocks)))
	(decreases (v remaining_len))
#reset-options "--z3timeout 200 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let rec counterblocks_contains_all_blocks i rgn x len remaining_len plain cipher = 
  let x0 = {x with ctr=ctr_0 i +^ 1ul} in
  (* let all_blocks = counterblocks i rgn x0 (v len) 0 (v len) plain cipher in *)
  (* let completed_len = v x0.ctr - v (offset i) in *)
  (* let n_blocks = v x.ctr - v x0.ctr in *)
  counterblocks_len rgn x0 (v len) 0 plain cipher;
  incr_remaining_len_ok x len remaining_len;
  if remaining_len = 0ul then ()
  else let l = min remaining_len (PRF.blocklen i) in 
       counterblocks_contains_all_blocks i rgn (PRF.incr i x) len (remaining_len -^ l) plain cipher;
       admit() //NS: significant --- but will change for Plan A

let from_x_blocks_included_in (#i:id) (#rgn:rid) (x:PRF.domain i) (blocks:prf_blocks rgn i) (blocks':prf_blocks rgn i) = 
  forall (y:PRF.domain i).{:pattern (find blocks y)}
       y `above` x /\
       v y.ctr <= v (ctr_0 i +^ 1ul) + Seq.length blocks
       ==> find blocks y == find blocks' y
  
#reset-options "--z3timeout 200 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
val widen_contains_all_blocks:   #i:id -> #r:rid ->
				 (x_init:PRF.domain i{x_init.ctr = PRF.ctr_0 i +^ 1ul}) ->
				 (x:PRF.domain i{x `above` x_init}) ->
				 (len:u32) -> (remaining_len:u32{remaining_len_ok x len remaining_len}) ->
				 (p:maybe_plain i (v len)) ->
				 (cipher:lbytes (v len)) ->
				 (blocks: prf_blocks r i) ->
				 (blocks':prf_blocks r i) ->
      Lemma (requires (let completed_len = v len - v remaining_len in
       		       let n_blocks = v x.ctr - v (offset i) in
       		       Seq.length blocks >= num_blocks' i (v len) /\
		       contains_all_blocks x len remaining_len p cipher blocks /\
		       from_x_blocks_included_in x_init blocks blocks'))
	    (ensures (contains_all_blocks x len remaining_len p cipher blocks'))
	    (decreases (v remaining_len))
let rec widen_contains_all_blocks #i #r x_init x len remaining_len p cipher blocks blocks'
    = if not (safeId i) || remaining_len = 0ul then 
	 () 
      else let starting_pos = len -^ remaining_len in
	   let l = min remaining_len (PRF.blocklen i) in
	   (*  *)
	   widen_contains_all_blocks #i #r x_init (PRF.incr i x) len (remaining_len -^ l) p cipher blocks blocks'

#set-options "--initial_ifuel 0 --max_ifuel 0 --initial_fuel 2 --max_fuel 2"
let find_singleton (#rgn:region) (#i:id) (e:PRF.entry rgn i) (x:PRF.domain i) 
    : Lemma (if is_entry_domain x e then PRF.find (Seq.create 1 e) x == Some e.range
	     else PRF.find (Seq.create 1 e) x == None)
    = ()	     

#set-options "--initial_ifuel 0 --max_ifuel 0 --initial_fuel 0 --max_fuel 0"
val intro_contains_all_blocks: (i:id{safeId i}) ->
		  	       (n:Cipher.iv (alg i)) ->
			       (st:state i Reader) ->
	      		       #aadlen:UInt32.t {aadlen <=^ aadmax} ->
			       (aad:lbuffer (v aadlen)) ->
			       #plainlen:UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
			       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) ->
			       (q:maybe_plain i (v plainlen)) ->
			       (entry:entry i) ->
			       (blocks: prf_blocks st.prf.mac_rgn i) ->
			       (h:mem{Buffer.live h cipher_tagged}) ->
     Lemma (requires (let aead_entries = HS.sel h st.log in 
		      let prf_entries = HS.sel h (PRF.itable i st.prf) in 
		      let x_1 = {iv=n; ctr=ctr_0 i +^ 1ul} in
		      Buffer.live h aad /\
		      refines_one_entry h entry blocks /\
		      find_entry n aead_entries == Some entry /\
		      found_entry n st aad cipher_tagged q h /\
		      from_x_blocks_included_in x_1 blocks prf_entries))
           (ensures (let x1 = {iv=n; ctr=ctr_0 i +^ 1ul} in
		     let cipher = Buffer.sub cipher_tagged 0ul plainlen in
		     contains_all_blocks' x1 plainlen plainlen q cipher st.prf h))

#set-options "--initial_ifuel 0 --max_ifuel 0 --initial_fuel 0 --max_fuel 0"
let intro_contains_all_blocks i n st #aadlen aad #plainlen cipher_tagged q entry blocks h =
  let Entry nonce ad l p c = entry in
  let prf_entries = HS.sel h (PRF.itable i st.prf) in 
  assert (nonce == n);
  assert (c == Buffer.as_seq h cipher_tagged);
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in
  let c' = Buffer.as_seq h cipher in
    (* *)
  let blocks_hd = SeqProperties.head blocks in 
  let blocks_tl = SeqProperties.tail blocks in
  let x_1 = {iv=n; ctr=ctr_0 i +^ 1ul} in
  assert (blocks_tl == counterblocks i st.prf.mac_rgn x_1 (v plainlen) 0 (v plainlen) p c');
  assert (Seq.equal (Seq.slice blocks_tl 0 (Seq.length blocks_tl)) blocks_tl);
  counterblocks_contains_all_blocks i st.prf.mac_rgn x_1 plainlen plainlen p c'; 
  (*  *)
  let widen_blocks_tl_blocks (y:domain i)
    : Lemma (y `above` x_1 ==> PRF.find blocks y == PRF.find blocks_tl y)  
    = if y `above` x_1 
      then (assert (Seq.equal blocks (SeqProperties.cons blocks_hd blocks_tl));
	    find_singleton blocks_hd y;
	    find_append y (Seq.create 1 blocks_hd) blocks_tl) in
  FStar.Classical.forall_intro widen_blocks_tl_blocks;
  widen_contains_all_blocks x_1 x_1 plainlen plainlen q c' blocks_tl blocks;
  widen_contains_all_blocks x_1 x_1 plainlen plainlen q c' blocks prf_entries

val entry_exists_if_verify_ok : #i:id -> #n:Cipher.iv (alg i) -> (st:state i Reader) ->
 			        #aadlen:UInt32.t {aadlen <=^ aadmax} -> (aad:lbuffer (v aadlen)) ->
			        #plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
			       (plain:Plain.plainBuffer i (v plainlen)) ->
			       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) ->
			       (ak:CMA.state (i,n)) ->
			       (acc:CMA.accBuffer (i, n)) ->
			       (tag:lbuffer 16{tag == Buffer.sub cipher_tagged plainlen MAC.taglen}) ->
			       (h:mem{verify_liveness ak tag h /\ 
				      decrypt_requires_live st aad plain cipher_tagged h /\
				      safeId i}) ->
    Lemma (requires (my_inv st h /\
		     CMA.acc_inv ak acc h /\
		     accumulate_encoded aad #plainlen (Buffer.sub cipher_tagged 0ul plainlen) acc h /\
		     verify_ok ak acc tag h true /\
		     is_mac_for_iv st ak h))
          (ensures (my_inv st h /\
		    (let entries = HS.sel h st.log in 
		     match find_entry n entries with
		     | None -> False
		     | Some (Entry _ _ l p _) ->
		       l == v plainlen /\
		       found_entry n st aad cipher_tagged p h)))
let entry_exists_if_verify_ok #i #n st #aadlen aad #plainlen plain cipher_tagged_b ak acc tag_b h =
    let entries = HS.sel h st.log in
    let prf_table = HS.sel h (PRF.itable i st.prf) in
    let x0 = {iv = n; ctr=ctr_0 i} in
    let cipher_tagged = Buffer.as_seq h cipher_tagged_b in
    let cipher, _ = SeqProperties.split cipher_tagged (v plainlen) in
    let tag = Buffer.as_seq h tag_b in
    let ( e, blocks ) = find_entry_blocks i st.prf.mac_rgn n entries prf_table h in
    let ak' = PRF.macRange st.prf.mac_rgn i x0 (Seq.index blocks 0).range in
    assert (ak == ak');
    let Entry nonce aad' plainlen' p' cipher_tagged' = e in
    let cipher', _ = SeqProperties.split cipher_tagged' plainlen' in
    let mac_log = CMA.ilog (CMA.State.log ak) in
    match m_sel h mac_log with
    | None           -> ()
    | Some (msg,tag') -> 
      lemma_encode_both_inj i aadlen plainlen (u (Seq.length aad')) (u plainlen')
			     (Buffer.as_seq h aad) cipher aad' cipher';
      assert (Seq.equal tag tag');
      assert (Seq.equal cipher cipher');
      assert (Seq.equal cipher_tagged' (Seq.append cipher' tag'));
      assert (Seq.equal cipher_tagged (Seq.append cipher tag))

val get_verified_plain : #i:id -> #n:Cipher.iv (alg i) -> st:state i Reader ->
 			 #aadlen:UInt32.t {aadlen <=^ aadmax} -> (aad:lbuffer (v aadlen)) ->
			 #plainlen:UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
			 plain:Plain.plainBuffer i (v plainlen) ->
			 cipher_tagged:lbuffer (v plainlen + v MAC.taglen) ->
		         ak:CMA.state (i,n) ->
			 acc:CMA.accBuffer (i, n) ->
			 verified:bool ->
      ST (maybe_plain i (v plainlen))
         (requires (fun h -> 
		    let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in 
	            decrypt_requires_live st aad plain cipher_tagged h /\ 
		    (if safeId i && verified
		     then verify_liveness ak tag h /\ 
		  	  is_mac_for_iv st ak h /\
			  my_inv st h /\
			  CMA.acc_inv ak acc h /\
			  accumulate_encoded aad #plainlen (Buffer.sub cipher_tagged 0ul plainlen) acc h /\
			  verify_ok ak acc tag h true
	             else True)))
         (ensures (fun h0 p h1 -> 
		    let cipher = Buffer.sub cipher_tagged 0ul plainlen in
		    let x1 = {iv=n; ctr=ctr_0 i +^ 1ul} in
		    h0 == h1 /\
		    (if verified
		     then contains_all_blocks' x1 plainlen plainlen p cipher st.prf h1 /\
		          (safeId i ==> found_entry n st aad cipher_tagged p h1)
		     else True)))
#set-options "--initial_fuel 1 --max_fuel 1"	     
let get_verified_plain #i #n st #aadlen aad #plainlen plain cipher_tagged ak acc verified = 
  if safeId i && verified then
    let h = get () in
    let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in 
    entry_exists_if_verify_ok st aad plain cipher_tagged ak acc tag h;
    let entries = !st.log in 
    let (Some (Entry _nonce _ad _l p _c)) = find_entry n entries in
    let _ : unit = 
      let prf_table = HS.sel h (PRF.itable i st.prf) in
      let ( e, blocks ) = find_entry_blocks i st.prf.mac_rgn n entries prf_table h in
      intro_contains_all_blocks i n st aad cipher_tagged p e blocks h in
    p
  else if safeId i then 
     Plain.load plainlen plain
  else ()

val establish_post_condition: #i:id -> #n:Cipher.iv (alg i) -> (st:state i Reader) -> 
			      #aadlen:UInt32.t {aadlen <=^ aadmax} -> (aad:lbuffer (v aadlen)) ->
 			      #plainlen:UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
			      (plain:plainBuffer i (v plainlen)) ->
			      (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) ->
			      (p:maybe_plain i (v plainlen)) ->
			      (ak:CMA.state (i, n)) ->
			      (acc:CMA.accBuffer (i, n)) ->
			      (verified:bool) -> (h2:mem) -> (h3:mem) -> (h4:mem) ->
   Lemma (requires (let cipher = Buffer.sub cipher_tagged 0ul plainlen in
		     let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in
		     let x = PRF.incr i ({iv=n; ctr=ctr_0 i}) in
		     decrypt_requires_live st aad plain cipher_tagged h3 /\
		     decrypt_requires_sep st aad plain cipher_tagged /\
		     verify_ensures ak acc tag h2 verified h3 /\
		     HS (is_stack_region h3.tip) /\
		     (safeId i ==> is_mac_for_iv st ak h3) /\
		     (safeId i ==> accumulate_encoded aad #plainlen cipher acc h3) /\
		     my_inv st h3 /\
		     (if verified
		      then (safeId i ==> found_entry n st aad cipher_tagged p h3) /\
			   counter_dexor_ensures i st.prf x plainlen plain cipher p h3 h4
		      else h3 == h4)))
          (ensures (my_inv st h4 /\
		    decrypt_ok n st aad plain cipher_tagged verified h4))
let establish_post_condition #i #n st #aadlen aad #plainlen plain cipher_tagged p ak acc verified h2 h3 h4 =
  if not verified
  then ()
  else if safeId i || not (prf i)
  then (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer plain) h3 h4;
        if safeId i then begin
	   let entries = HS.sel h3 st.log in 
           let blocks = HS.sel h3 (PRF (itable i st.prf)) in 
	   frame_refines i st.prf.mac_rgn entries blocks h3 h4;
	   decrypted_up_to_end plain p h4
	end)
  else FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer plain) h3) h4

let frame_myinv_pop (#i:id) (#r:rw) (st:state i r) (h:mem{HS.poppable h})
   : Lemma (requires (my_inv st h))
	   (ensures (my_inv st (HS.pop h)))
   = if safeId i
     then frame_refines i st.prf.mac_rgn (HS.sel h st.log) (HS.sel h (PRF.itable i st.prf)) h (HS.pop h)

let frame_decrypt_ok (#i:id) (n:Cipher.iv (alg i)) (st:state i Reader) 
	       (#aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen))
	       (#plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)}) 
	       (plain:plainBuffer i (v plainlen))
	       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
	       (verified:bool) (h:mem{HS.poppable h})
   : Lemma (requires (decrypt_requires_sep st aad plain cipher_tagged /\
		      decrypt_requires_live st aad plain cipher_tagged h /\
		      decrypt_ok n st aad plain cipher_tagged verified h))
	   (ensures (decrypt_ok n st aad plain cipher_tagged verified (HS.pop h)))
   = ()	   

#reset-options "--z3timeout 1000 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let prf_mac_modifies (i:id) (t:PRF.state i) (h0:mem) (h1:mem) = 
  Crypto.AEAD.BufferUtils.prf_mac_modifies (safeId i) t.rgn h0 h1

let adapt_dexor_modifies (#i:id) (#len:u32) (t:PRF.state i) (x:PRF.domain i) 
			 (pb:plainBuffer i (v len)) (h0:mem) (h1:mem)
     : Lemma (dexor_modifies t x pb h0 h1
	      ==> Crypto.AEAD.BufferUtils.dexor_modifies (safeId i) t.rgn (as_buffer pb) h0 h1)
     = FStar.Classical.move_requires (FStar.Buffer.lemma_reveal_modifies_1 (as_buffer pb) h0) h1

val chain_modification: (i:id) -> (n:Cipher.iv (alg i)) -> (st:state i Reader) ->
		        #aadlen:UInt32.t {aadlen <=^ aadmax} -> (aad:lbuffer (v aadlen)) ->
		        #plainlen:UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
		       (plain:plainBuffer i (v plainlen)) ->
		       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) ->
		       (h_init:mem) -> (h0:mem) ->(h1:mem)-> (h2:mem) -> (h3:mem) -> (h4:mem) ->
     Lemma (requires
	    (let x1 = {iv=n; ctr=ctr_0 i +^ 1ul} in
	    decrypt_requires_sep st aad plain cipher_tagged /\
	    decrypt_requires_live st aad plain cipher_tagged h_init /\
	    HS.fresh_frame h_init h0 /\
	    prf_mac_modifies i st.prf h0 h1 /\
	    Buffer.modifies_0 h1 h2 /\
	    Buffer.modifies_0 h2 h3 /\
	    (h3 == h4 \/ dexor_modifies st.prf x1 plain h3 h4)))
	    (ensures (HS.poppable h4 /\
		      decrypt_modifies st plain h_init (HS.pop h4)))
let chain_modification i n st #aadlen aad #plainlen plain cipher_tagged h_init h0 h1 h2 h3 h4 =
    let x1 = {iv=n; ctr=ctr_0 i +^ 1ul} in
    adapt_dexor_modifies st.prf x1 plain h3 h4;
    Crypto.AEAD.BufferUtils.chain_modification (safeId i) st.log_region (as_buffer plain) h_init h0 h1 h2 h3 h4


val frame_my_inv: (i:id) -> (st:state i Reader) -> (h0:mem) ->(h1:mem)-> (h2:mem) -> (h3:mem) -> 
     Lemma (requires
	    (HS.is_eternal_region st.log_region /\
  	     HS (st.log_region `is_in` h0.h) /\
 	     HS (is_stack_region h0.tip) /\
 	     prf_mac_modifies i st.prf h0 h1 /\
	     (prf i ==> h1 `HS.contains` (PRF.itable i st.prf)) /\
	     (h0 == h1 \/ HS.modifies_ref st.prf.mac_rgn TSet.empty h0 h1) /\
	     Buffer.modifies_0 h1 h2 /\
	     Buffer.modifies_0 h2 h3 /\
	     my_inv st h0))
	    (ensures (my_inv st h3))
let frame_my_inv i st h0 h1 h2 h3 = 
  FStar.Buffer.lemma_reveal_modifies_0 h1 h2;
  FStar.Buffer.lemma_reveal_modifies_0 h2 h3;
  if safeId i 
  then frame_refines i st.prf.mac_rgn (HS.sel h0 st.log) (HS.sel h0 (PRF.itable i st.prf)) h0 h3

val frame_acc: #i: MAC.id -> st: CMA.state i -> #aadlen:aadlen_32 -> aad:lbuffer (v aadlen) ->
	       #txtlen:txtlen_32 -> cipher:lbuffer (v txtlen) -> 
	       (h0:mem) -> (a:CMA.accBuffer i) -> (h1:mem) -> h2:mem -> 
    Lemma (requires (accumulate_ensures st aadlen aad txtlen cipher h0 a h1 /\	       
		     Buffer.modifies_0 h1 h2))
          (ensures (accumulate_ensures st aadlen aad txtlen cipher h0 a h2))
let frame_acc #i st #aalen aad #txtlent cipher h0 a h1 h2 = 
  FStar.Buffer.lemma_reveal_modifies_0 h0 h1;
  FStar.Buffer.lemma_reveal_modifies_0 h1 h2;
  FStar.Buffer.lemma_intro_modifies_0 h0 h2;
  if mac_log 
  then (assert (h1  `HS.contains` CMA.alog a);
        assert (HS.sel h2 (CMA.alog a) == HS.sel h1 (CMA.alog a));
	assert (Buffer.as_seq h2 (MAC.as_buffer (CMA st.r)) ==
	        Buffer.as_seq h1 (MAC.as_buffer (CMA st.r)));
	assert (Buffer.as_seq h2 (MAC.as_buffer (CMA a.a)) ==
	        Buffer.as_seq h1 (MAC.as_buffer (CMA a.a)));
        MAC.frame_sel_elem h1 h2 (CMA st.r);
        MAC.frame_sel_elem h1 h2 (CMA a.a))
  else ()

val decrypt:
  i:id -> st:state i Reader ->
  n:Cipher.iv (alg i) ->
  aadlen:UInt32.t {aadlen <=^ aadmax} ->
  aad:lbuffer (v aadlen) ->
  plainlen:UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
  plain:plainBuffer i (v plainlen) ->
  cipher_tagged:lbuffer (v plainlen + v MAC.taglen) ->
  ST bool
  (requires (fun h ->
    decrypt_requires_sep st aad plain cipher_tagged /\
    decrypt_requires_live st aad plain cipher_tagged h /\
    my_inv st h /\
    decrypt_when_auth i n st h))
  (ensures (fun h0 verified h1 ->
    my_inv st h1 /\
    decrypt_requires_live st aad plain cipher_tagged h1 /\
    decrypt_modifies st plain h0 h1 /\
    decrypt_ok n st aad plain cipher_tagged verified h1))
#reset-options "--z3timeout 1000 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let decrypt i st iv aadlen aad plainlen plain cipher_tagged =
  let h_init = get() in
  push_frame();
  let h0 = get () in
  frame_myinv_push st h_init h0;
  let x = PRF({iv = iv; ctr = ctr_0 i}) in // PRF index to the first block
  let ak = prf_mac_wrapper i st.prf st.ak x in   // used for keying the one-time MAC
  let h1 = get() in 
  assert (prf_mac_modifies i st.prf h0 h1);
  assert (safeId i ==> is_mac_for_iv st ak h1);
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in
  let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in
  assert(CMA(MAC.norm h1 ak.r));
// First recompute and check the MAC
  let acc = accumulate_wrapper ak aadlen aad plainlen cipher in
  let h2 = ST.get() in
  assert (safeId i ==> accumulate_encoded aad #plainlen cipher acc h2);
  Buffer.lemma_reveal_modifies_0 h1 h2;
  let verified = verify_wrapper ak acc tag in
  let h3 = ST.get() in
  Buffer.lemma_reveal_modifies_0 h2 h3;
  frame_my_inv i st h0 h1 h2 h3; //my_inv st h3
  frame_acc #(i, iv) ak #aadlen aad #plainlen cipher h1 acc h2 h3;
  // then, safeID i /\ stateful invariant ==>
  //    not verified ==> no entry in the AEAD table
  //    verified ==> exists Entry(iv ad l p c) in AEAD.log
  //                 and correct entries above x in the PRF table
  //                 with matching aad, cipher, and plain
  //
  // not sure what we need to prove for 1st level of PRF idealization
  // possibly that the PRF table with ctr=0 matches the Entry table.
  // (PRF[iv,ctr=0].MAC.log =  Some(l,t) iff Entry(iv,___))
  let p = get_verified_plain st aad plain cipher_tagged ak acc verified in 
  if verified 
  then begin
    let y = PRF.incr i x in	   
    counter_dexor i st.prf y plainlen plainlen plain cipher p
  end;
  let h4 = get() in
  establish_post_condition st aad plain cipher_tagged p ak acc verified h2 h3 h4;
  pop_frame();
  frame_myinv_pop st h4;
  frame_decrypt_ok iv st aad plain cipher_tagged verified h4;
  chain_modification i iv st aad plain cipher_tagged h_init h0 h1 h2 h3 h4;
  verified
