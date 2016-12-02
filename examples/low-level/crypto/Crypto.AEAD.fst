module Crypto.AEAD

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

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module Spec = Crypto.Symmetric.Poly1305.Spec
module MAC = Crypto.Symmetric.Poly1305.MAC

module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF

type region = rgn:HH.rid {HS.is_eternal_region rgn}

let ctr x = PRF.(x.ctr)

//16-10-12 TEMPORARY, while PRF remains somewhat CHACHA-specific
//16-10-12 NB we are importing this restriction from Encoding too
let id = Crypto.AEAD.Encoding.id

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
 (* n defined in FStar.UInt128, so is shadowed. Thus, we have to rename n into n' *)
assume val lt_pow2_index_to_vec: n':nat -> x:UInt128.t -> Lemma
  (requires FStar.UInt128.(v x < pow2 n'))
  (ensures  FStar.UInt128.(forall (i:nat). (i < 128 /\ i >= n') ==>
    Seq.index (FStar.UInt.to_vec (v x)) (127-i) = false))

// TODO: prove, generalize and move
assume val index_to_vec_lt_pow2: n:nat -> x:FStar.BitVector.bv_t 128 -> Lemma
  (requires (forall (i:nat). (i < 128 /\ i >= n) ==> Seq.index x (127-i) = false))
  (ensures  (FStar.UInt.from_vec x < pow2 n))

// TODO: move
 (* n defined in FStar.UInt128, so is shadowed. Thus, we have to rename n into n' *)
val lemma_xor_bounded: n':nat -> x:UInt128.t -> y:UInt128.t -> Lemma
  (requires FStar.UInt128.(v x < pow2 n' /\ v y < pow2 n'))
  (ensures  FStar.UInt128.(v (logxor x y) < pow2 n'))
let lemma_xor_bounded n x y =
  let n' = n in
  let open FStar.BitVector in
  let open FStar.UInt128 in
  let vx = FStar.UInt.to_vec (v x) in
  let vy = FStar.UInt.to_vec (v y) in
  let n = n' in (* n defined in FStar.UInt128, so was shadowed, so renamed into n' *)
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
  let log = ralloc rgn (Seq.createEmpty #(entry i)) in
  let prf = PRF.gen rgn i in 
  //16-10-16 let ak = MAC.akey_gen rgn i in
  State #i #Writer #rgn log prf 

val coerce: i:id{~(prf i)} -> rgn:region -> key:lbuffer (v (PRF.keylen i)) -> ST (state i Writer)
  (requires (fun h -> Buffer.live h key))
  (ensures  (fun h0 st h1 -> True))
let coerce i rgn key = 
  let log = ralloc rgn (Seq.createEmpty #(entry i)) in // Shouldn't exist
  let prf = PRF.coerce rgn i key in
  //16-10-16 let ak = MAC.akey_gen rgn i // should actually split key into two.
  State #i #Writer #rgn log prf

#reset-options "--z3rlimit 20"

val genReader: #i:id -> st:state i Writer -> ST (state i Reader)
  (requires (fun _ -> True))
  (ensures  (fun _ _ _ -> True))
let genReader #i st =
  State #i #Reader #st.log_region st.log st.prf

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
  i:id -> t:PRF.state i -> x:PRF.domain i{x.ctr <> 0ul} ->
  len:u32{len <> 0ul /\ safelen i (v len) 1ul} ->
  remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len} ->
  plain:plainBuffer i (v len) ->
  cipher:lbuffer (v len)
  { let bp = as_buffer plain in 
    Buffer.disjoint bp cipher /\
    Buffer.frameOf bp <> (PRF.(t.rgn)) /\
    Buffer.frameOf cipher <> (PRF.(t.rgn)) 
  } -> 
  h_init:mem ->
//  STL unit -- NS: should be in STL, but the rest of the library isn't really in STL yet
  ST unit
  (requires (fun h -> 
    let initial_domain = {x with ctr=1ul} in
    let completed_len = len -^ remaining_len in 
    Plain.live h plain /\ 
    Buffer.live h cipher /\ 
    (remaining_len <> 0ul ==> FStar.Mul.((v x.ctr - 1) * v (PRF.blocklen i) = v completed_len)) /\
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
    let initial_domain = {x with ctr=1ul} in
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
#set-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
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

//TODO: Move this to AEAD.Invariant
val inv: h:mem -> #i:id -> #rw:rw -> e:state i rw -> Tot Type0
let inv h #i #rw e =
  match e with
  | State #i_ #rw_ #log_region log prf ->
    safeId i ==>
    ( let r = itable i_ prf in 
      let blocks = HS.sel h r in
      let entries = HS.sel h log in
      h `HS.contains` r /\
      refines h i (PRF.(prf.mac_rgn)) entries blocks )

let prf_state (#i:id) (#rw:rw) (e:state i rw) : PRF.state i = State?.prf e

val counter_dexor: 
  i:id -> t:PRF.state i -> x:PRF.domain i{x.ctr <> 0ul} -> len:u32{safelen i (v len) x.ctr} ->
  plain:plainBuffer i (v len) -> 
  cipher:lbuffer (v len) 
  { let bp = as_buffer plain in 
    Buffer.disjoint bp cipher /\
    Buffer.frameOf bp <> (PRF.(t.rgn)) /\
    Buffer.frameOf cipher <> (PRF.(t.rgn)) 
  } -> STL unit
  (requires (fun h -> 
    Plain.live h plain /\ 
    Buffer.live h cipher /\ 
    // if ciphertexts are authenticated, then the table already includes all we need
    (safeId i ==> (let expected = counterblocks i t.mac_rgn x (v len) 0 (v len) (Plain.sel_plain h len plain) (Buffer.as_seq h cipher) in
                True //TODO say that expected is found in the table
    ))))
  (ensures (fun h0 _ h1 -> 
    Plain.live h1 plain /\ 
    Buffer.live h1 cipher /\ 
    // in all cases, we extend the table only at x and its successors.
    modifies_table_above_x_and_buffer t x (as_buffer plain) h0 h1 /\
    (safeId i ==> Seq.equal #(PRF.entry (PRF.(t.mac_rgn)) i) (HS.sel h1 t.table) (HS.sel h0 t.table))))
  
let rec counter_dexor i t x len plaintext ciphertext =
  assume false;//16-10-12 
  if len <> 0ul 
  then
    begin // at least one more block
      let l = min len (PRF.blocklen i) in 
      let cipher = Buffer.sub ciphertext 0ul l  in 
      let plain = Plain.sub plaintext 0ul l in 

      (*
      recall (PRF.(t.table)); //16-09-22 could this be done by ! ??
      let s = PRF.( !t.table ) in
      let h = ST.get() in
      // WARNING: moving the PRF.find_otp outside the assume will segfault
      // at runtime, because t.table doesn't exist in real code
      assume(match PRF.find_otp #(PRF.State?.rgn t) #i s x with
        | Some (PRF.OTP l' p c) -> l == l' /\ c = sel_bytes h l cipher
        | None -> False);
      *)
      PRF.prf_dexor i t x l plain cipher;

      let len = len -^ l in 
      let ciphertext = Buffer.sub ciphertext l len in
      let plaintext = Plain.sub plaintext l len in
      counter_dexor i t (PRF.incr i x) len plaintext ciphertext
    end


// ENCRYPT AND DECRYPT
// some code duplication, but in different typing contexts
//16-09-18 not yet using ideal state.

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
    inv h #i #Writer st /\
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

let encrypt i st n aadlen aad plainlen plain cipher_tagged =
  (* push_frame(); *)
  assume (safeId i);
  assume (prf i);
  let h0 = get() in
  let x = PRF.({iv = n; ctr = 0ul}) in // PRF index to the first block
  let ak = PRF.prf_mac i st.prf x in  // used for keying the one-time MAC
  let h1 = get () in 
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
  intro_refines_one_entry_no_tag #i st n (v plainlen) plain cipher_tagged h0 h1 h2; //we have pre_refines_one_entry here
  assert (Buffer.live h1 aad); //seem to need this hint
  assume (HS.(is_stack_region h2.tip)); //TODO: remove this once we move all functions to STL
  let l, acc = accumulate ak aadlen aad plainlen cipher in
  let h3 = get() in
  let _ = 
    let c = Buffer.as_seq h3 cipher in
    let ad = Buffer.as_seq h3 aad in
    assert (l == field_encode i ad #plainlen c) in
  assert (Buffer.live h2 aad); //seem to need this hint
  assert (Buffer.live h3 aad); //seem to need this hint
  Buffer.lemma_reveal_modifies_0 h2 h3;
  MAC.mac ak l acc tag;
  let h4 = get () in 
  assert (Buffer.live h4 aad);
  assert (Buffer.live h4 cipher_tagged);
  assert (Plain.live h4 plain);
  let _ = 
    let tab = HS.sel h4 (itable i st.prf) in
    match PRF.find_mac tab x with 
    | None -> assert False
    | Some mac_st -> () in
  assume false

(*
      // no need to be so specific here --- details follow from the invariant
      let c = Buffer.as_seq h1 (Buffer.sub ciphertext 0ul plainlen) in 
      let t: lbuffer 16 = Buffer.as_seq h1 (Buffer.sub ciphertext plainlen (Spec.taglen i)) in
      let a = Buffer.as_seq h1 aadtext in
      let l = field_encode i a c in (
      match PRF.find_0 (HS.sel h1 (PRF.State?.table e.prf)) (PRF.({iv=n; ctr=0ul})) with 
      | Some mac -> 
          let log = MAC.ilog (MAC.State?.log mac) in 
          m_contains log h1 /\ m_sel h1 log == Some (l,t)
      | None -> False))
*)      

val decrypt: 
  i:id -> e:state i Reader -> 
  n:Cipher.iv (alg i) -> 
  aadlen:UInt32.t {aadlen <=^ aadmax} -> 
  aadtext:lbuffer (v aadlen) -> 
  plainlen:UInt32.t {safelen i (v plainlen) 1ul} -> 
  plaintext:plainBuffer i (v plainlen) -> 
  ciphertext:lbuffer (v plainlen + v (Spec.taglen i)) 
  { Buffer.disjoint aadtext ciphertext /\
    Buffer.disjoint_2 (Plain.as_buffer plaintext) aadtext ciphertext }
  -> STL bool
  (requires (fun h -> 
    inv h #i #Reader e /\
    Buffer.live h aadtext /\
    Buffer.live h ciphertext /\ 
    Plain.live h plaintext ))
  (ensures (fun h0 verified h1 -> 
    inv h1 #i #Reader e /\
    Buffer.live h1 aadtext /\
    Buffer.live h1 ciphertext /\ 
    Plain.live h1 plaintext /\
    Buffer.modifies_1 (Plain.as_buffer plaintext) h0 h1 /\
    (safeId i ==> (
        let found = find (HS.sel h1 e.log) n in
        if verified then
          let a = Buffer.as_seq h1 aadtext in
          let p = Plain.sel_plain h1 plainlen plaintext in
          let c = Buffer.as_seq h1 ciphertext in
          found == Some (Entry n a (v plainlen) p c)
        else
          found == None /\ h0 == h1 ))))


let decrypt i st iv aadlen aad plainlen plain cipher_tagged =
  push_frame();
  let x = PRF.({iv = iv; ctr = 0ul}) in // PRF index to the first block
  let ak = PRF.prf_mac i st.prf x in   // used for keying the one-time MAC
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in 
  let tag = Buffer.sub cipher_tagged plainlen (Spec.taglen i) in 

  // First recompute and check the MAC
  let h0 = ST.get() in
  assume(
    MAC.(Buffer.live h0 ak.r /\ norm h0 ak.r) /\
    Buffer.live h0 aad /\ Buffer.live h0 cipher);

  let l, acc = accumulate ak aadlen aad plainlen cipher in

  let h = ST.get() in 
  assert(mac_log ==> l = encode_both aadlen (Buffer.as_seq h aad) plainlen (Buffer.as_seq h cipher));

  let verified = MAC.verify ak l acc tag in

  // let h1 = ST.get() in
  // assert(mac_log /\ MAC.authId (i,iv) ==> (verified == (HS.sel h1 (MAC.(ilog ak)) = Some (l,tag))));  

  // then, safeID i /\ stateful invariant ==>
  //    not verified ==> no entry in the AEAD table
  //    verified ==> exists Entry(iv ad l p c) in AEAD.log 
  //                 and correct entries above x in the PRF table
  //                 with matching aad, cipher, and plain
  //
  // not sure what we need to prove for 1st level of PRF idealization
  // possibly that the PRF table with ctr=0 matches the Entry table. 
  // (PRF[iv,ctr=0].MAC.log =  Some(l,t) iff Entry(iv,___)) 

  assume false; //16-10-16 
  if verified then counter_dexor i st.prf (PRF.incr i x) plainlen plain cipher;
  pop_frame();
  verified
