module Crypto.AEAD

// We implement ideal AEAD on top of ideal Chacha20 and ideal Poly1305. 
// We precisely relate AEAD's log to their underlying state.

// This file intends to match the spec of AEAD0.fst in mitls-fstar. 

open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.Monotonic.RRef

open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Plain
open Flag

open Crypto.Symmetric.PRF
open Crypto.AEAD.Encoding 
open Crypto.AEAD.Invariant
open Crypto.AEAD.Lemmas
open Crypto.AEAD.Lemmas.Part2

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module MAC = Crypto.Symmetric.MAC
module CMA = Crypto.Symmetric.UF1CMA

module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF

type region = rgn:HH.rid {HS.is_eternal_region rgn}

let ctr x = PRF(x.ctr)

////////////////////////////////////////////////////////////////////////////////
//Wrappers for experimentation, to be moved back to their original locations

//Move back to UF1CMA
let mac_ensures (i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:MAC.tagB)
		(h0:mem) (h1:mem) = 
    let open FStar.Buffer in
    let open Crypto.Symmetric.Bytes in
    let open Crypto.Symmetric.Poly1305 in
    let open Crypto.Symmetric.UF1CMA in
    Buffer.live h0 st.s /\ 
    MAC.live h0 st.r /\ 
    Buffer.live h1 tag /\
    CMA.acc_inv st acc h0 /\ (
    if mac_log then
      HS.modifies (as_set [st.region; Buffer.frameOf tag]) h0 h1 /\
      (* mods_2 [HS.Ref (as_hsref (ilog st.log)); HS.Ref (Buffer.content tag)] h0 h1 /\ *)
      Buffer.modifies_buf_1 (Buffer.frameOf tag) tag h0 h1 /\
      HS.modifies_ref st.region !{HS.as_ref (as_hsref (ilog st.log))} h0 h1 /\
      m_contains (ilog st.log) h1 /\ (
      let log = FStar.HyperStack.sel h1 (alog acc) in
      let a = MAC.sel_elem h1 acc.a in
      let r = MAC.sel_elem h1 st.r in
      let s = Buffer.as_seq h1 st.s in
      let t = MAC.mac log r s in
      sel_word h1 tag === t /\
      m_sel h1 (ilog st.log) == Some(log,t))
      (* let mac = mac_1305 l (sel_elem h0 st.r) (sel_word h0 st.s) in *)
      (* mac == little_endian (sel_word h1 tag) /\ *)
      (* m_sel h1 (ilog st.log) == Some (l, sel_word h1 tag)) *)
    else Buffer.modifies_1 tag h0 h1)
#reset-options "--z3timeout 40 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let mac_wrapper (#i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:MAC.tagB)
  : ST unit
  (requires (fun h0 ->
    let open Crypto.Symmetric.UF1CMA in
    Buffer.live h0 tag /\ 
    Buffer.live h0 st.s /\
    Buffer.disjoint_2 (MAC.as_buffer acc.a) st.s tag /\ 
    Buffer.disjoint (MAC.as_buffer st.r) tag /\
    Buffer.disjoint st.s tag /\ 
    acc_inv st acc h0 /\
    (mac_log ==> m_contains (ilog st.log) h0) /\
    (mac_log /\ authId i ==> m_sel h0 (ilog st.log) == None)))
  (ensures (fun h0 _ h1 -> mac_ensures i st acc tag h0 h1))
  = let open Crypto.Symmetric.UF1CMA in
    let h0 = get () in
    CMA.mac #i st acc tag;
    let h1 = get () in 
    if mac_log then begin
      (* Need to update UF1CMA to prove this (problem with the mods clause not working fully) *)
      assume (Buffer.modifies_buf_1 (Buffer.frameOf tag) tag h0 h1);
      assume (HS.modifies_ref st.region !{HS.as_ref (as_hsref (ilog st.log))} h0 h1)
    end

//Move back to Crypto.AEAD.Encoding
let alog_fresh (#a:Type0) h0 h1 (r:HS.reference a) = 
    HS.frameOf r == HS h1.tip /\
    h1 `HS.contains` r /\
  ~ (h0 `HS.contains` r)

let accumulate_ensures (#i: MAC.id) (st: CMA.state i) (aadlen:aadlen_32) (aad:lbuffer (v aadlen))
		       (txtlen:txtlen_32) (cipher:lbuffer (v txtlen))
		       (h0:mem) (a:CMA.accBuffer i) (h1:mem) =
  Buffer.modifies_0 h0 h1 /\ // modifies only fresh buffers on the current stack
  ~ (h0 `Buffer.contains` (CMA (MAC.as_buffer (a.a)))) /\
  Buffer.live h1 aad /\ 
  Buffer.live h1 cipher /\
  Buffer.frameOf (CMA (MAC.as_buffer a.a)) = HS h1.tip /\
  CMA.acc_inv st a h1 /\
  (mac_log ==> 
    alog_fresh h0 h1 (CMA.alog a) /\
    FStar.HyperStack.sel h1 (CMA.alog a) ==
    encode_both (fst i) aadlen (Buffer.as_seq h1 aad) txtlen (Buffer.as_seq h1 cipher))

let accumulate_wrapper (#i: MAC.id) (st: CMA.state i) (aadlen:aadlen_32) (aad:lbuffer (v aadlen))
		       (txtlen:txtlen_32) (cipher:lbuffer (v txtlen)) 
   : StackInline (CMA.accBuffer i)
      (requires (fun h0 -> 
	  CMA(MAC.norm h0 st.r) /\
	  Buffer.live h0 aad /\ 
	  Buffer.live h0 cipher))
      (ensures (fun h0 a h1 ->  accumulate_ensures #i st aadlen aad txtlen cipher h0 a h1))
  = let h0 = get () in
    let acc = accumulate #i st aadlen aad txtlen cipher in
    let h1 = get () in
    assert (Buffer.disjoint_2 (MAC.as_buffer (CMA acc.a)) (CMA st.s) cipher);
    assume (mac_log ==> alog_fresh h0 h1 (CMA.alog acc));
    acc

//Done with wrappers
////////////////////////////////////////////////////////////////////////////////


//16-10-12 TEMPORARY, while PRF remains somewhat CHACHA-specific
//16-10-12 NB we are importing this restriction from Encoding too
//let id = Crypto.AEAD.Encoding.id

// ********* StreamAE **********
//
// (Definitions adapted from TLS/StreamAE.fst, to be integrated later)
//
// The per-record nonce for the AEAD construction is formed as follows:
//
// 1. The 64-bit record sequence number is padded to the left with zeroes to iv_length.
//
// 2. The padded sequence number is XORed with the static client_write_iv or server_write_iv,
//    depending on the role.
//
// The XORing is a fixed, ad hoc, random permutation; not sure what is gained;
// we can reason about sequence-number collisions before applying it.

// TODO: prove, generalize and move
assume val lt_pow2_index_to_vec: n:nat -> x:UInt128.t -> Lemma
  (requires FStar.UInt128(v x < pow2 n))
  (ensures  FStar.UInt128(forall (i:nat). (i < 128 /\ i >= n) ==>
    Seq.index (FStar.UInt.to_vec (v x)) (127-i) = false))

// TODO: prove, generalize and move
assume val index_to_vec_lt_pow2: n:nat -> x:FStar.BitVector.bv_t 128 -> Lemma
  (requires (forall (i:nat). (i < 128 /\ i >= n) ==> Seq.index x (127-i) = false))
  (ensures  (FStar.UInt.from_vec x < pow2 n))

// TODO: move
val lemma_xor_bounded: n:nat -> x:UInt128.t -> y:UInt128.t -> Lemma
  (requires FStar.UInt128(v x < pow2 n /\ v y < pow2 n))
  (ensures  FStar.UInt128(v (logxor x y) < pow2 n))
let lemma_xor_bounded n x y =
  let open FStar.BitVector in
  let open FStar.UInt128 in
  let vx = FStar.UInt.to_vec (v x) in
  let vy = FStar.UInt.to_vec (v y) in
  lt_pow2_index_to_vec n x;
  lt_pow2_index_to_vec n y;
  lemma_xor_bounded 128 n vx vy;
  index_to_vec_lt_pow2 n (logxor_vec vx vy)

//16-10-05 by induction on n, given a bitwise definition of logxor.

//16-10-12 computes nonce from static IV and sequence number
let aeIV i (seqn:UInt64.t) (staticIV:Cipher.iv (alg i)) : Tot (Cipher.iv (alg i)) =
  let x = FStar.Int.Cast.uint64_to_uint128 seqn in
  let r = UInt128.logxor x staticIV in
  assert(FStar.UInt128.v staticIV < pow2 96);
  assert(FStar.UInt128.v x < pow2 64);
  assume(FStar.UInt128.v x < pow2 96);
  lemma_xor_bounded 96 x staticIV; 
  r

assume val aeIV_injective: i:id -> seqn0:UInt64.t -> seqn1:UInt64.t -> staticIV:Cipher.iv (alg i) -> Lemma
  (aeIV i seqn0 staticIV = aeIV i seqn1 staticIV ==> seqn0 = seqn1)
//let aeIV_injective i seqn0 seqn1 staticIV = ()

  (* relying on 0 xor 0 = 0 for the higher-order bytes *) 
  (* recheck endianness *)

// a bit more concrete than the spec: xor only 64 bits, copy the rest. 
 
// PLAN: 
//
// We allocate AEAD logs at the writer (complying with our `local modifier' discipline)
// We allocate all PRF tables in a global private region (to escape that discipline)

// Global state invariant: 
// for all ideal instances of AEAD, 
// - their regions and PRFs tables are pairwise disjoint; and
// - their PRF table contents correctly refines their AEAD logs,
//     (up to early decryptor allocations in initial state)

// Lemma: this invariant depends only on AEAD-writer regions and the PRF region. 
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
//
// Needed: prf_read returning a ghost of the actual underlying block. 

// TODO: switch to conditional idealization

//let sub s start len = Seq.slice start (start+len) s // more convenient? 

// REPRESENTATIONS 

// LOW-LEVEL? We use high-level (immutable) bytes for convenience, but
// we try to remain compatible with stack-based implementations, 

let find (#i:id) (s:Seq.seq (entry i)) (n:Cipher.iv (alg i)) : option (entry i) =
  SeqProperties.seq_find (fun (e:entry i) -> e.nonce = n) s 

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

(* notes 16-10-04 

Not sure what's the best style to push as an invariant.
It may be easier to first split blocks by iv. 

This corresponds to the PRF state "at rest" for the invariant.
Should be uniform between i:id {MAC.ideal /\ authId i }.

For the dexor loop, we have as `pre` that the PRF state contains the correct entries.
We need as a monotonic invariant that "containing implies finding"; more like map than seq.

For the enxor loop, we need a finer, transient invariant for the last chunk of the PRF log. 

*) 

(*
let lookupIV (i:id) (s:Seq.seq (entry i)) = Seq.seq_find (fun e:entry i -> e.iv = iv) s // <- requires iv:UInt128.t
*)

// COUNTER_MODE LOOP from Chacha20 

(*
let ctr_inv ctr len = 
  len =^ 0ul \/
  ( 0ul <^ ctr /\
    v ctr + v(len /^ PRF.blocklen) < v PRF.maxCtr)  //we use v... to avoid ^+ overflow
*)

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
//  STL unit -- NS: should be in STL, but the rest of the library isn't really in STL yet
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
  (* *)
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

//TODO: Move this to AEAD.Invariant
val inv: h:mem -> #i:id -> #rw:rw -> e:state i rw -> Tot Type0
let inv h #i #rw e =
  match e with
  | State #i_ #rw_ #log_region log prf ak ->
    safeId i ==>
    ( let r = itable i_ prf in 
      let blocks = HS.sel h r in
      let entries = HS.sel h log in
      h `HS.contains` r /\
      refines h i (PRF prf.mac_rgn) entries blocks )

let prf_state (#i:id) (#rw:rw) (e:state i rw) : PRF.state i = State.prf e
////////////////////////////////////////////////////////////////////////////////

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

let my_inv (#i:id) (#rw:_) (st:state i rw) (h:mem) = 
  inv h st /\
  HS (h.h `Map.contains` st.prf.mac_rgn) /\
  (safeId i ==> h `HS.contains` st.log) /\
  (prf i ==> h `HS.contains` (itable i st.prf))


let encrypt_ensures (i:id) (st:state i Writer)
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
     HS.modifies_transitively (as_set [st.log_region; Buffer.frameOf cipher_tagged; HS h5.tip]) h0 h5 /\ (
     safeId i ==>  (
       let aad = Buffer.as_seq h5 aad in
       let p = Plain.sel_plain h5 plainlen plain in
       let c = Buffer.as_seq h5 cipher_tagged in
       HS.sel h5 st.log == SeqProperties.snoc (HS.sel h0 st.log) (Entry n aad (v plainlen) p c)))

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
    HS.modifies_transitively (as_set [st.log_region; Buffer.frameOf cipher_tagged; HS h4.tip]) h0 h3 /\
    HS.modifies_ref st.prf.mac_rgn TSet.empty h0 h3 /\
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
              encrypt_ensures i st n aadlen aad plainlen plain cipher_tagged h0 h5))

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

let modifies_push_pop (h:HS.mem) (h0:HS.mem) (h5:HS.mem) (r:Set.set HH.rid)
  : Lemma (requires (HS.fresh_frame h h0 /\
		     HS.modifies_transitively (Set.union r (Set.singleton (HS h0.tip))) h0 h5))
          (ensures (HS.poppable h5 /\ HS.modifies_transitively r h (HS.pop h5)))
  = ()

let encrypt_ensures' (i:id) (st:state i Writer)
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
     HS.modifies_transitively (as_set [st.log_region; Buffer.frameOf cipher_tagged]) h0 h5 /\ (
     safeId i ==>  (
       let aad = Buffer.as_seq h5 aad in
       let p = Plain.sel_plain h5 plainlen plain in
       let c = Buffer.as_seq h5 cipher_tagged in
       HS.sel h5 st.log == SeqProperties.snoc (HS.sel h0 st.log) (Entry n aad (v plainlen) p c)))

let rec frame_refines' (i:id{safeId i}) (mac_rgn:region) 
		      (entries:Seq.seq (entry i)) (blocks:Seq.seq (PRF.entry mac_rgn i))
		      (h:mem) (h':mem)
   : Lemma (requires refines h i mac_rgn entries blocks /\
		     HH.modifies_rref mac_rgn TSet.empty (HS h.h) (HS h'.h) /\
		     HS.live_region h' mac_rgn)
	   (ensures  refines h' i mac_rgn entries blocks)
	   (decreases (Seq.length entries))
   = admit()

let frame_myinv_push (i:id) (st:state i Writer) (h:mem) (h1:mem)
   : Lemma (requires (my_inv st h /\ 
		      HS.fresh_frame h h1))
	   (ensures (my_inv st h1))
   = if safeId i
     then frame_refines' i st.prf.mac_rgn (HS.sel h st.log) (HS.sel h (PRF.itable i st.prf)) h h1

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
		      encrypt_ensures i st n aadlen aad plainlen plain cipher_tagged h0 h5))
	   (ensures (HS.poppable h5 /\
		     encrypt_ensures'  i st n aadlen aad plainlen plain cipher_tagged h (HS.pop h5)))
   = if safeId i
     then frame_refines' i st.prf.mac_rgn (HS.sel h5 st.log) (HS.sel h5 (PRF.itable i st.prf)) h5 (HS.pop h5)

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
  //STL -- should be STL eventually, but this requires propagation throughout the library
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
    encrypt_ensures' i st n aadlen aad plainlen plain cipher_tagged h0 h5))
    (* Buffer.m_ref (Buffer.frameOf cipher) !{Buffer.modifies_1 cipher h0 h1 /\  *)
(* #reset-options "--z3timeout 1000 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0" *)
let encrypt i st n aadlen aad plainlen plain cipher_tagged =
  let h_init = get() in
  push_frame();
  let h0 = get () in
  frame_myinv_push i st h_init h0;
  assert (HH.modifies_rref st.prf.mac_rgn TSet.empty (HS h_init.h) (HS h0.h));
  assert (HS (is_stack_region h0.tip));
  assert (HS (HH.disjoint h0.tip st.log_region));
  assert (HS (HH.disjoint h0.tip (Buffer.frameOf cipher_tagged)));
  let x = PRF({iv = n; ctr = ctr_0 i}) in // PRF index to the first block
  let ak = PRF.prf_mac i st.prf st.ak x in  // used for keying the one-time MAC
  let h1 = get () in
  (* assume (Buffer.live h1 (CMA ak.s)); //TODO: need to add liveness post-conditions in UF1CMA.genPost *)
  (* assume (Buffer.disjoint (MAC.as_buffer (CMA ak.r)) (CMA ak.s)); //TODO: need to add separation to UF1CMA.State *)
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
  assume (MAC.norm h2 (CMA ak.r)); //TODO: need to revise the definition of norm to work with an abstract type of elemB
  let acc = accumulate_wrapper ak aadlen aad plainlen cipher in
  //Establishing the pre-conditions of MAC.mac
  let h3 = get() in
  Buffer.lemma_reveal_modifies_0 h2 h3;
  assert (HS.modifies_transitively (as_set [st.log_region; Buffer.frameOf cipher_tagged; HS h3.tip]) h0 h3);
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
  
(* //////////////////////////////////////////////////////////////////////////////// *)
(* val counter_dexor:  *)
(*   i:id -> t:PRF.state i -> x:PRF.domain i{PRF.ctr_0 i <^ x.ctr} -> len:u32{safelen i (v len) x.ctr} -> *)
(*   plain:plainBuffer i (v len) ->  *)
(*   cipher:lbuffer (v len)  *)
(*   { let bp = as_buffer plain in  *)
(*     Buffer.disjoint bp cipher /\ *)
(*     Buffer.frameOf bp <> (PRF t.rgn) /\ *)
(*     Buffer.frameOf cipher <> (PRF t.rgn)  *)
(*   } -> STL unit *)
(*   (requires (fun h ->  *)
(*     Plain.live h plain /\  *)
(*     Buffer.live h cipher /\  *)
(*     // if ciphertexts are authenticated, then the table already includes all we need *)
(*     (safeId i ==> (let expected = counterblocks i t.mac_rgn x (v len) 0 (v len) (Plain.sel_plain h len plain) (Buffer.as_seq h cipher) in *)
(*                 True //TODO say that expected is found in the table *)
(*     )))) *)
(*   (ensures (fun h0 _ h1 ->  *)
(*     Plain.live h1 plain /\  *)
(*     Buffer.live h1 cipher /\  *)
(*     // in all cases, we extend the table only at x and its successors. *)
(*     modifies_table_above_x_and_buffer t x (as_buffer plain) h0 h1 /\ *)
(*     (safeId i ==> Seq.equal #(PRF.entry (PRF t.mac_rgn) i) (HS.sel h1 t.table) (HS.sel h0 t.table)))) *)
  
(* let rec counter_dexor i t x len plaintext ciphertext = *)
(*   assume false;//16-10-12  *)
(*   if len <> 0ul  *)
(*   then *)
(*     begin // at least one more block *)
(*       let l = min len (PRF.blocklen i) in  *)
(*       let cipher = Buffer.sub ciphertext 0ul l  in  *)
(*       let plain = Plain.sub plaintext 0ul l in  *)

(*       (\* *)
(*       recall (PRF t.table); //16-09-22 could this be done by ! ?? *)
(*       let s = PRF !t.table in *)
(*       let h = ST.get() in *)
(*       // WARNING: moving the PRF.find_otp outside the assume will segfault *)
(*       // at runtime, because t.table doesn't exist in real code *)
(*       assume(match PRF.find_otp #(PRF.State.rgn t) #i s x with *)
(*         | Some (PRF.OTP l' p c) -> l == l' /\ c = sel_bytes h l cipher *)
(*         | None -> False); *)
(*       *\) *)
(*       PRF.prf_dexor i t x l plain cipher; *)

(*       let len = len -^ l in  *)
(*       let ciphertext = Buffer.sub ciphertext l len in *)
(*       let plaintext = Plain.sub plaintext l len in *)
(*       counter_dexor i t (PRF.incr i x) len plaintext ciphertext *)
(*     end *)


(* // ENCRYPT AND DECRYPT *)

(* val encrypt:  *)
(*   i: id -> st:state i Writer ->  *)
(*   n: Cipher.iv (alg i) -> *)
(*   aadlen: UInt32.t {aadlen <=^ aadmax} ->  *)
(*   aad: lbuffer (v aadlen) ->  *)
(*   plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->  *)
(*   plain: plainBuffer i (v plainlen) ->  *)
(*   cipher:lbuffer (v plainlen + v MAC.taglen)  *)
(*   {  *)
(*     Buffer.disjoint aad cipher /\ *)
(*     Buffer.disjoint (Plain.as_buffer plain) aad /\ *)
(*     Buffer.disjoint (Plain.as_buffer plain) cipher /\ *)
(*     HH.disjoint (Buffer.frameOf (Plain.as_buffer plain)) st.log_region /\ *)
(*     HH.disjoint (Buffer.frameOf cipher) st.log_region /\ *)
(*     HH.disjoint (Buffer.frameOf aad) st.log_region *)
(*   } *)
(*   ->   *)
(*   //STL -- should be STL eventually, but this requires propagation throughout the library *)
(*   ST unit *)
(*   (requires (fun h ->  *)
(*     let prf_rgn = st.prf.rgn in *)
(*     inv h #i #Writer st /\ *)
(*     Buffer.live h aad /\ *)
(*     Buffer.live h cipher /\  *)
(*     Plain.live h plain /\ *)
(*     (prf i ==> none_above ({iv=n; ctr=ctr_0 i}) st.prf h) // The nonce must be fresh! *)
(*    )) *)
(*   (ensures (fun h0 _ h1 ->  *)
(*     //TODO some "heterogeneous" modifies that also records updates to logs and tables *)
(*     Buffer.modifies_1 cipher h0 h1 /\  *)
(*     Buffer.live h1 aad /\ *)
(*     Buffer.live h1 cipher /\  *)
(*     Plain.live h1 plain /\ *)
(*     inv h1 #i #Writer st /\  *)
(*     (safeId i ==> ( *)
(*       let aad = Buffer.as_seq h1 aad in *)
(*       let p = Plain.sel_plain h1 plainlen plain in *)
(*       let c = Buffer.as_seq h1 cipher in *)
(*       HS.sel h1 st.log == SeqProperties.snoc (HS.sel h0 st.log) (Entry n aad (v plainlen) p c))) *)
(*    )) *)

(* let encrypt i st n aadlen aad plainlen plain cipher_tagged = *)
(*   (\* push_frame(); *\) *)

(*   assume false;//16-10-31  *)
(*   // assume (safeId i); *)
(*   // assume (prf i); *)
  
(*   let h0 = get() in *)
(*   let x = PRF({iv = n; ctr = ctr_0 i}) in // PRF index to the first block *)
(*   let ak = PRF.prf_mac i st.prf st.ak x in  // used for keying the one-time MAC *)
(*   let h1 = get () in  *)
(*   let cipher = Buffer.sub cipher_tagged 0ul plainlen in *)
(*   let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in *)
(*   let y = PRF.incr i x in *)
(*   //calling this lemma allows us to complete the proof without using any fuel;  *)
(*   //which makes things a a bit faster *)
(*   counterblocks_emp i st.prf.mac_rgn y (v plainlen) 0  *)
(*       (Plain.sel_plain h1 plainlen plain) (Buffer.as_seq h1 cipher); *)
(*   counter_enxor i st.prf y plainlen plainlen plain cipher h1; *)
(*   // Compute MAC over additional data and ciphertext *)
(*   let h2 = get () in *)
(*   intro_refines_one_entry_no_tag #i st n (v plainlen) plain cipher_tagged h0 h1 h2; //we have pre_refines_one_entry here *)
(*   assert (Buffer.live h1 aad); //seem to need this hint *)
(*   assume (HS (is_stack_region h2.tip)); //TODO: remove this once we move all functions to STL *)
(*   assume (CMA(MAC.norm h0 ak.r)); *)
(*   let acc = accumulate ak aadlen aad plainlen cipher in *)
(*   let h3 = get() in *)
(*   let _ =  *)
(*     let c = Buffer.as_seq h3 cipher in *)
(*     let ad = Buffer.as_seq h3 aad in *)
(*     assert (FStar.HyperStack.sel h1 (CMA.alog acc) == encode_both i aadlen ad plainlen c) in *)
(*   assert (Buffer.live h2 aad); //seem to need this hint *)
(*   assert (Buffer.live h3 aad); //seem to need this hint *)
(*   Buffer.lemma_reveal_modifies_0 h2 h3; *)
(*   CMA.mac ak acc tag; *)
(*   let h4 = get () in  *)
(*   assert (Buffer.live h4 aad); *)
(*   assert (Buffer.live h4 cipher_tagged); *)
(*   assert (Plain.live h4 plain); *)
(*   let _ =  *)
(*     let tab = HS.sel h4 (itable i st.prf) in *)
(*     match PRF.find_mac tab x with  *)
(*     | None -> assert False *)
(*     | Some mac_st -> () in *)
(*   assume false *)


(* (\* *)
(*       // no need to be so specific here --- details follow from the invariant *)
(*       let c = Buffer.as_seq h1 (Buffer.sub ciphertext 0ul plainlen) in  *)
(*       let t: lbuffer 16 = Buffer.as_seq h1 (Buffer.sub ciphertext plainlen (Spec.taglen i)) in *)
(*       let a = Buffer.as_seq h1 aadtext in *)
(*       let l = field_encode i a c in ( *)
(*       match PRF.find_0 (HS.sel h1 (PRF.State.table e.prf)) (PRF({iv=n; ctr=0ul})) with  *)
(*       | Some mac ->  *)
(*           let log = MAC.ilog (MAC.State.log mac) in  *)
(*           m_contains log h1 /\ m_sel h1 log == Some (l,t) *)
(*       | None -> False)) *)
(* *\)       *)

(* val decrypt:  *)
(*   i:id -> e:state i Reader ->  *)
(*   n:Cipher.iv (alg i) ->  *)
(*   aadlen:UInt32.t {aadlen <=^ aadmax} ->  *)
(*   aadtext:lbuffer (v aadlen) ->  *)
(*   plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->  *)
(*   plaintext:plainBuffer i (v plainlen) ->  *)
(*   ciphertext:lbuffer (v plainlen + v MAC.taglen)  *)
(*   { Buffer.disjoint aadtext ciphertext /\ *)
(*     Buffer.disjoint_2 (Plain.as_buffer plaintext) aadtext ciphertext } *)
(*   -> STL bool *)
(*   (requires (fun h ->  *)
(*     inv h #i #Reader e /\ *)
(*     Buffer.live h aadtext /\ *)
(*     Buffer.live h ciphertext /\  *)
(*     Plain.live h plaintext )) *)
(*   (ensures (fun h0 verified h1 ->  *)
(*     inv h1 #i #Reader e /\ *)
(*     Buffer.live h1 aadtext /\ *)
(*     Buffer.live h1 ciphertext /\  *)
(*     Plain.live h1 plaintext /\ *)
(*     Buffer.modifies_1 (Plain.as_buffer plaintext) h0 h1 /\ *)
(*     (safeId i ==> ( *)
(*         let found = find (HS.sel h1 e.log) n in *)
(*         if verified then *)
(*           let a = Buffer.as_seq h1 aadtext in *)
(*           let p = Plain.sel_plain h1 plainlen plaintext in *)
(*           let c = Buffer.as_seq h1 ciphertext in *)
(*           found == Some (Entry n a (v plainlen) p c) *)
(*         else *)
(*           found == None /\ h0 == h1 )))) *)


(* let decrypt i st iv aadlen aad plainlen plain cipher_tagged = *)
(*   push_frame(); *)
(*   let x = PRF({iv = iv; ctr = ctr_0 i}) in // PRF index to the first block *)
(*   let ak = PRF.prf_mac i st.prf st.ak x in   // used for keying the one-time MAC *)
(*   let cipher = Buffer.sub cipher_tagged 0ul plainlen in  *)
(*   let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in  *)

(*   // First recompute and check the MAC *)
(*   let h0 = ST.get() in *)
(*   assume( *)
(*     CMA(MAC.live h0 ak.r /\ MAC.norm h0 ak.r) /\ *)
(*     Buffer.live h0 aad /\ Buffer.live h0 cipher); *)

(*   let acc = accumulate ak aadlen aad plainlen cipher in *)

(*   let h1 = ST.get() in  *)
(*   assert(mac_log ==>  FStar.HyperStack.sel h1 (CMA.alog acc) == encode_both i aadlen (Buffer.as_seq h1 aad) plainlen (Buffer.as_seq h1 cipher)); *)

(*   let verified = CMA.verify ak acc tag in *)

(*   // let h1 = ST.get() in *)
(*   // assert(mac_log /\ MAC.authId (i,iv) ==> (verified == (HS.sel h1 (MAC(ilog ak)) = Some (l,tag))));   *)

(*   // then, safeID i /\ stateful invariant ==> *)
(*   //    not verified ==> no entry in the AEAD table *)
(*   //    verified ==> exists Entry(iv ad l p c) in AEAD.log  *)
(*   //                 and correct entries above x in the PRF table *)
(*   //                 with matching aad, cipher, and plain *)
(*   // *)
(*   // not sure what we need to prove for 1st level of PRF idealization *)
(*   // possibly that the PRF table with ctr=0 matches the Entry table.  *)
(*   // (PRF[iv,ctr=0].MAC.log =  Some(l,t) iff Entry(iv,___))  *)

(*   assume false; //16-10-16  *)
(*   if verified then counter_dexor i st.prf (PRF.incr i x) plainlen plain cipher; *)
(*   pop_frame(); *)
(*   verified *)
