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

open Crypto.AEAD.Encoding 

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module Spec = Crypto.Symmetric.Poly1305.Spec
module MAC = Crypto.Symmetric.Poly1305.MAC

module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF

type region = rgn:HH.rid {HS.is_eternal_region rgn}

let ctr x = PRF(x.ctr)

//16-10-12 TEMPORARY, while PRF remains somewhat CHACHA-specific
//16-10-12 NB we are importing this restriction from Encoding too
let id = i:id {i.cipher = CHACHA20_POLY1305}


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
    
noeq type entry (i:id) =
  | Entry: 
      nonce:Cipher.iv (alg i) -> 
      ad:adata -> 
      l:plainLen -> 
      p:plain i l -> 
      c:cipher i (Seq.length (as_bytes p)) -> 
      entry i

let find (#i:id) (s:Seq.seq (entry i)) (n:Cipher.iv (alg i)) : option (entry i) =
  SeqProperties.seq_find (fun (e:entry i) -> e.nonce = n) s 

type rw = | Reader | Writer 

noeq type state (i:id) (rw:rw) =
  | State:
      #log_region: rgn -> // this is the *writer* region; the reader allocates nothing
      log: HS.ref (Seq.seq (entry i)) {HS.frameOf log == log_region} ->
      // Was PRF(prf.rgn) == region. Do readers use its own PRF state?
      prf: PRF.state i {PRF(prf.rgn) == log_region} (* including its key *) ->
      //16-10-16 ak: MAC.akey log_region i (* static, optional authentication key *) -> 
      state i rw


//16-09-18 where is it in the libraries??
private let min (a:u32) (b:u32) = if a <=^ b then a else b
private let minNat (a:nat) (b:nat) : nat = if a <= b then a else b

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


val genReader: #i:id -> st:state i Writer -> ST (state i Reader)
  (requires (fun _ -> True))
  (ensures  (fun _ _ _ -> True))
let genReader #i st =
  State #i #Reader #st.log_region st.log st.prf


// INVARIANT (WIP)
 
let maxplain (i:id) = pow2 14 // for instance

let safelen (i:id) (l:nat) (c:UInt32.t{0ul <^ c /\ c <=^ PRF.maxCtr i}) = 
  l = 0 || (
    let bl = v (Cipher( blocklen (cipher_of_id i))) in
    FStar.Mul(
      l + (v (c -^ 1ul)) * bl <= maxplain i && 
      l  <= v (PRF.maxCtr i -^ c) * bl ))
    
// Computes PRF table contents for countermode encryption of 'plain' to 'cipher' starting from 'x'.
val counterblocks: 
  i:id {safeId i} -> 
  rgn:region ->  //the rgn is really superfluous, 
		//since it is only potentially relevant in the case of the mac, 
		//but that's always Seq.createEmpty here
                //16-10-13 but still needed in the result type, right?
  x:PRF.domain i{ctr x >^ 0ul} -> 
  l:nat {safelen i l (ctr x)} -> 
  plain:Plain.plain i l -> 
  cipher:lbytes l -> 
  Tot (Seq.seq (PRF.entry rgn i)) // each entry e {PRF(e.x.id = x.iv /\ e.x.ctr >= ctr x)}
  (decreases l)

let rec counterblocks i rgn x l plain cipher = 
  let blockl = v (Cipher(blocklen (cipher_of_id i))) in 
  if l = 0 then
    Seq.createEmpty
  else 
    let l0 = minNat l blockl in 
    let l_32 = UInt32.uint_to_t l0 in 
    let block = PRF.Entry x (PRF.OTP l_32 (Plain.slice plain 0 l0) (Seq.slice cipher 0 l0)) in
    let cipher: lbytes(l - l0) = Seq.slice cipher l0 l in
    let plain = Plain.slice plain l0 l in
    // assert(safelen i (l - l0) (PRF(x.ctr +^ 1ul)));
    let blocks = counterblocks i rgn (PRF.incr i x) (l - l0) plain cipher in
    SeqProperties.cons block blocks

// States consistency of the PRF table contents vs the AEAD entries
// (not a projection from one another because of allocated MACs and aad)
val refines: 
  h:mem -> 
  i:id {safeId i} -> rgn:region ->
  entries: Seq.seq (entry i) -> 
  blocks: Seq.seq (PRF.entry rgn i) -> GTot Type0
  (decreases (Seq.length entries))

let num_blocks (#i:id) (e:entry i) : Tot nat = 
  let Entry nonce ad l plain cipher_tagged = e in
  let bl = v (Cipher( blocklen (cipher_of_id i))) in
  (l + bl - 1) / bl

let refines_one_entry (#rgn:region) (#i:id{safeId i}) (h:mem) (e:entry i) (blocks:Seq.seq (PRF.entry rgn i)) = 
  let Entry nonce ad l plain cipher_tagged = e in
  let b = num_blocks e in 
  b + 1 = Seq.length blocks /\
  (let PRF.Entry x e = Seq.index blocks 0 in
   PRF (x.iv = nonce) /\
   PRF (x.ctr = 0ul)  /\ (
   let xors = Seq.slice blocks 1 (b+1) in 
   let cipher, tag = SeqProperties.split cipher_tagged l in
   safelen i l 1ul /\
   xors == counterblocks i rgn (PRF.incr i x) l plain cipher /\ //NS: forced to use propositional equality here, since this compares sequences of abstract plain texts. CF 16-10-13: annoying, but intuitively right?
                                         
   (let m = PRF.macRange rgn i x e in
    let mac_log = MAC.ilog (MAC.State.log m) in
    m_contains mac_log h /\ (
    match m_sel h (MAC.ilog (MAC.State.log m)) with
    | None           -> False
    | Some (msg,tag') -> msg = field_encode i ad plain /\
			tag = tag')))) //NS: adding this bit to relate the tag in the entries to the tag in that MAC log

let rec refines h i rgn entries blocks = 
  if Seq.length entries = 0 then 
    Seq.length blocks == 0 //NS:using == to get it to match with the Type returned by the other branch
  else let e = SeqProperties.head entries in
       let b = num_blocks e in 
       b < Seq.length blocks /\
       (let blocks_for_e = Seq.slice blocks 0 (b + 1) in
       	let entries_tl = SeqProperties.tail entries in
        let remaining_blocks = Seq.slice blocks (b+1) (Seq.length blocks) in
        refines_one_entry h e blocks_for_e /\
	refines h i rgn entries_tl remaining_blocks)

let refines_empty (h:mem) (i:id{safeId i}) (rgn:region) 
  : Lemma (refines h i rgn Seq.createEmpty Seq.createEmpty)
  = ()

let rec block_lengths (#i:id{safeId i}) (entries:Seq.seq (entry i)) 
  : Tot nat (decreases (Seq.length entries))
  = if Seq.length entries = 0 then
      0
    else let e = SeqProperties.head entries in
	 num_blocks e + 1 + block_lengths (SeqProperties.tail entries)

#set-options "--z3timeout 20 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let rec refines_length (#rgn:region) (#i:id{safeId i}) (h:mem) 
		       (entries:Seq.seq (entry i)) (blocks:Seq.seq (PRF.entry rgn i))
   : Lemma (requires (refines h i rgn entries blocks))
	   (ensures (block_lengths entries = Seq.length blocks))
  	   (decreases (Seq.length entries))
   = if Seq.length entries = 0 then 
       ()
     else let hd = SeqProperties.head entries in
	  let entries_tl = SeqProperties.tail entries in
	  let b = num_blocks hd in
	  let blocks_tail = Seq.slice blocks (b + 1) (Seq.length blocks) in
	  refines_length h entries_tl blocks_tail

#set-options "--z3timeout 100 --initial_fuel 2 --max_fuel 2 --initial_ifuel 0 --max_ifuel 0"
let refines__singleton (h:mem) (i:id{safeId i}) (rgn:region) (e:entry i) (blocks_for_e:Seq.seq (PRF.entry rgn i))
  : Lemma (requires (refines_one_entry h e blocks_for_e))
	  (ensures (refines h i rgn (Seq.create 1 e) blocks_for_e))
  = let b = num_blocks e in 
    cut (Seq.equal (Seq.slice blocks_for_e 0 (b + 1)) blocks_for_e)

let frame_refines_one_entry (h:mem) (i:id{safeId i}) (mac_rgn:region) 
			    (e:entry i) (blocks:Seq.seq (PRF.entry mac_rgn i))
			    (h':mem)
   : Lemma (requires refines_one_entry h e blocks /\			    
		     HS.modifies_ref mac_rgn TSet.empty h h' /\
		     HS.live_region h' mac_rgn)
	   (ensures  refines_one_entry h' e blocks)
   = let PRF.Entry x rng = Seq.index blocks 0 in
     let m = PRF.macRange mac_rgn i x rng in
     let mac_log = MAC.ilog (MAC.State.log m) in
     assert (m_sel h mac_log = m_sel h' mac_log);
     assert (m_contains mac_log h') //this include HS.live_region, which is not derivable from modifies_ref along
     
#set-options "--z3timeout 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let rec extend_refines (h:mem) (i:id{safeId i}) (mac_rgn:region) 
		    (entries:Seq.seq (entry i))
		    (blocks:Seq.seq (PRF.entry mac_rgn i))
		    (e:entry i)
		    (blocks_for_e:Seq.seq (PRF.entry mac_rgn i))
   		    (h':mem)
  : Lemma (requires refines h i mac_rgn entries blocks /\
		    refines_one_entry h' e blocks_for_e /\
		    HS.modifies_ref mac_rgn TSet.empty h h' /\
		    HS.live_region h' mac_rgn)
	  (ensures (refines h' i mac_rgn (SeqProperties.snoc entries e) (Seq.append blocks blocks_for_e)))
	  (decreases (Seq.length entries))
  = if Seq.length entries = 0 then
      (refines__singleton h' i mac_rgn e blocks_for_e;
       cut (Seq.equal (SeqProperties.snoc entries e) (Seq.create 1 e));
       cut (Seq.equal (Seq.append blocks blocks_for_e) blocks_for_e))
    else let hd = SeqProperties.head entries in
	 let entries_tl = SeqProperties.tail entries in
	 let b = num_blocks hd in
	 let blocks_hd = Seq.slice blocks 0 (b + 1) in
	 let blocks_tl = Seq.slice blocks (b + 1) (Seq.length blocks) in
	 assert (refines h i mac_rgn entries_tl blocks_tl);
	 frame_refines_one_entry h i mac_rgn hd blocks_hd h';
	 extend_refines h i mac_rgn entries_tl blocks_tl e blocks_for_e h';
	 assert (refines h' i mac_rgn (SeqProperties.snoc entries_tl e) (Seq.append blocks_tl blocks_for_e));
	 cut (Seq.equal (SeqProperties.snoc entries e) (SeqProperties.cons hd (SeqProperties.snoc entries_tl e)));
	 cut (SeqProperties.head (SeqProperties.snoc entries e) == hd);
	 cut (Seq.equal (SeqProperties.tail (SeqProperties.snoc entries e)) (SeqProperties.snoc entries_tl e));
	 let blocks_hd = Seq.slice blocks 0 (b + 1) in
	 let ext_blocks = Seq.append blocks blocks_for_e in
	 cut (Seq.equal ext_blocks
    			(Seq.append blocks_hd (Seq.append blocks_tl blocks_for_e)));
	 cut (Seq.equal (Seq.slice ext_blocks 0 (b + 1)) blocks_hd);
	 cut (Seq.equal (Seq.slice ext_blocks (b + 1) (Seq.length ext_blocks)) 
			(Seq.append blocks_tl blocks_for_e))



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

open Crypto.Symmetric.PRF

let all_above (#rgn:region) (#i:PRF.id) (s:Seq.seq (PRF.entry rgn i)) (x:domain i) = 
  (forall (e:PRF.entry rgn i).{:pattern (s `SeqProperties.contains` e)} 
     s `SeqProperties.contains` e ==> e.x `above` x)

let trans_all_above (#rgn:region) (#i:PRF.id) (s:Seq.seq (PRF.entry rgn i)) 
		    (x:domain i) (y:domain i{y `above` x})
    : Lemma (all_above s y ==> all_above s x)
    = ()

let modifies_table_above_x_and_buffer (#i:PRF.id) (t:PRF.state i) x b h0 h1 = 
  Buffer.live h1 b /\ 
  (if prf i then 
    let r = itable i t in 
    let rb = Buffer.frameOf b in 
    let rgns = Set.union (Set.singleton #HH.rid t.rgn) (Set.singleton #HH.rid rb) in 
    let contents0 = HS.sel h0 r in
    let contents1 = HS.sel h1 r in
    HS.modifies rgns h0 h1 /\ 
    HS.modifies_ref t.rgn (TSet.singleton (FStar.Heap.Ref (HS.as_ref r))) h0 h1 /\
    Seq.length contents0 <= Seq.length contents1 /\
    Seq.equal (Seq.slice contents1 0 (Seq.length contents0)) contents0 /\
    all_above (Seq.slice contents1 (Seq.length contents0) (Seq.length contents1)) x
  else
    Buffer.modifies_1 b h0 h1)

let refl_modifies_table_above_x_and_buffer (#i:PRF.id) (#l:nat) (t:PRF.state i) 
			     (x:PRF.domain i{x.ctr <> 0ul}) 
			     (c:lbuffer l)
			     (h:mem)
    : Lemma (requires (Buffer.live h c))
	    (ensures (modifies_table_above_x_and_buffer t x c h h))
    = if prf i then 
	let r = itable i t in
	let c0 = HS.sel h r in
	let emp = Seq.slice c0 (Seq.length c0) (Seq.length c0) in
	cut (Seq.equal Seq.createEmpty emp);
	FStar.Classical.forall_intro (SeqProperties.contains_elim emp)
      else ()
	
let trans_modifies_table_above_x_and_buffer (#i:PRF.id) (#l:nat) (t:PRF.state i) 
			     (x_0:PRF.domain i{x_0.ctr <> 0ul}) (x_1:PRF.domain i{x_1 `above` x_0})
			     (c:lbuffer l)
			     (h_0:mem) (h_1:mem) (h_2:mem)
    : Lemma (requires (modifies_table_above_x_and_buffer t x_0 c h_0 h_1 /\ 
		       modifies_table_above_x_and_buffer t x_1 c h_1 h_2))
	    (ensures (modifies_table_above_x_and_buffer t x_0 c h_0 h_2))
    = if prf i then
        let r = itable i t in 
        let c0 = HS.sel h_0 r in
	let c1 = HS.sel h_1 r in
	let c2 = HS.sel h_2 r in
	let diff_01 = Seq.slice c1 (Seq.length c0) (Seq.length c1) in
	let diff_12 = Seq.slice c2 (Seq.length c1) (Seq.length c2) in
	let diff_02 = Seq.slice c2 (Seq.length c0) (Seq.length c2) in
	assert (Seq.equal diff_02 (Seq.append diff_01 diff_12));
	FStar.Classical.forall_intro (SeqProperties.append_contains_equiv diff_01 diff_12)
      else ()

let x_buffer_1_modifies_table_above_x_and_buffer (#i:PRF.id) (#l:nat) (t:PRF.state i) 
			     (x:PRF.domain i{x.ctr <> 0ul})
			     (c:lbuffer l)
			     (h_0:mem) (h_1:mem)
    : Lemma (requires (modifies_x_buffer_1 t x c h_0 h_1))
	    (ensures  (modifies_table_above_x_and_buffer t x c h_0 h_1))
    = admit()

val counter_enxor: 
  i:id -> t:PRF.state i -> x:PRF.domain i{x.ctr <> 0ul} -> len:u32{safelen i (v len) x.ctr} ->
  plain:plainBuffer i (v len) -> 
  cipher:lbuffer (v len) 
  { let bp = as_buffer plain in 
    Buffer.disjoint bp cipher /\
    Buffer.frameOf bp <> (PRF t.rgn) /\
    Buffer.frameOf cipher <> (PRF t.rgn) 
  } -> 
//  STL unit -- NS: should be in STL, but the rest of the library isn't really in STL yet
  ST unit
  (requires (fun h -> 
    Plain.live h plain /\ 
    Buffer.live h cipher /\ 
    // if ciphertexts are authenticated, then fresh blocks are available
    (safeId i ==> (forall z. z `above` x ==> find_otp #t.mac_rgn #i (HS.sel h t.table) z == None))
    ))
  (ensures (fun h0 _ h1 -> 
    Plain.live h1 plain /\
    Buffer.live h1 cipher /\
    // in all cases, we extend the table only at x and its successors.
    modifies_table_above_x_and_buffer t x cipher h0 h1 /\
    // if ciphertexts are authenticated, then we precisely know the table extension
    (safeId i ==> HS.sel h1 t.table ==
    		  Seq.append (HS.sel h0 t.table)
    			     (counterblocks i t.mac_rgn x (v len) (Plain.sel_plain h1 len plain) (Buffer.as_seq h1 cipher)))
    // NB the post of prf_enxor should be strengthened a bit (using PRF.extends?)
    ))

let fresh_frame_modifies_table_above_x_and_buffer (#i:PRF.id) (#l:nat) (t:PRF.state i)
			     (x:PRF.domain i{x.ctr <> 0ul})
			     (c:lbuffer l)
			     (h_0:mem) (h_1:mem) (h_2:mem)
    : Lemma (requires (HS.fresh_frame h_0 h_1 /\ modifies_table_above_x_and_buffer t x c h_1 h_2))
	    (ensures (modifies_table_above_x_and_buffer t x c h_0 h_2))
    = admit()

let pop_frame_modifies_table_above_x_and_buffer (#i:PRF.id) (#l:nat) (t:PRF.state i)
			     (x:PRF.domain i{x.ctr <> 0ul})
			     (c:lbuffer l)
			     (h_0:mem) (h_1:mem) (h_2:mem)
    : Lemma (requires (modifies_table_above_x_and_buffer t x c h_0 h_1 /\ HS.poppable h_1 /\  h_2==HS.pop h_1))
	    (ensures (modifies_table_above_x_and_buffer t x c h_0 h_2))
    = admit()

#set-options "--z3timeout 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let rec counter_enxor i t x len plain cipher =
  let h_initial = get () in
  push_frame();
  let h0 = get () in
  if len <> 0ul then
    begin // at least one more block
      let l = min len (PRF.blocklen i) in 
      let cipher_hd = Buffer.sub cipher 0ul l in 
      let plain_hd = Plain.sub plain 0ul l in 
      (*
      recall (PRF t.table);
      let s = (PRF !t.table) in 
      assume(is_None(PRF.find s x));
      *)
      PRF.prf_enxor i t x l cipher_hd plain_hd;
      let h1 = get () in 
      x_buffer_1_modifies_table_above_x_and_buffer t x cipher h0 h1;
      (* assume (modifies_table_above_x_and_buffer t x cipher h0 h1); *)
      let len = len -^ l in 
      let cipher_tl = Buffer.sub cipher l len in
      let plain_tl = Plain.sub plain l len in
      let y = PRF.incr i x in
      let _ =
      	let h = get () in
      	assume (safeId i ==> (forall z. z `above` y ==> find_otp #t.mac_rgn #i (HS.sel h t.table) z == None)) in
      counter_enxor i t y len plain_tl cipher_tl;
      let h2 = get () in 
      trans_modifies_table_above_x_and_buffer t x y cipher h0 h1 h2
    end
  else refl_modifies_table_above_x_and_buffer t x cipher h0;
 let h1 = get () in
 fresh_frame_modifies_table_above_x_and_buffer t x cipher h_initial h0 h1;
 pop_frame();
 let h_final = get () in 
 pop_frame_modifies_table_above_x_and_buffer t x cipher h_initial h1 h_final;
 (* assume (modifies_table_above_x_and_buffer t x cipher h0 h1); *)
 assume (safeId i ==> HS.sel h_final t.table == 
    		      Seq.append (HS.sel h_initial t.table)
    			     (counterblocks i t.mac_rgn x (v len) (Plain.sel_plain h_final len plain) (Buffer.as_seq h_final cipher)))



val counter_dexor: 
  i:id -> t:PRF.state i -> x:PRF.domain i{x.ctr <> 0ul} -> len:u32{safelen i (v len) x.ctr} ->
  plain:plainBuffer i (v len) -> 
  cipher:lbuffer (v len) 
  { let bp = as_buffer plain in 
    Buffer.disjoint bp cipher /\
    Buffer.frameOf bp <> (PRF t.rgn) /\
    Buffer.frameOf cipher <> (PRF t.rgn) 
  } -> STL unit
  (requires (fun h -> 
    Plain.live h plain /\ 
    Buffer.live h cipher /\ 
    // if ciphertexts are authenticated, then the table already includes all we need
    (safeId i ==> (let expected = counterblocks i t.mac_rgn x (v len) (Plain.sel_plain h len plain) (Buffer.as_seq h cipher) in
                True //TODO say that expected is found in the table
    ))))
  (ensures (fun h0 _ h1 -> 
    Plain.live h1 plain /\ 
    Buffer.live h1 cipher /\ 
    // in all cases, we extend the table only at x and its successors.
    modifies_table_above_x_and_buffer t x (as_buffer plain) h0 h1 /\
    (safeId i ==> Seq.equal #(PRF.entry (PRF t.mac_rgn) i) (HS.sel h1 t.table) (HS.sel h0 t.table))))
  
let rec counter_dexor i t x len plaintext ciphertext =
  assume false;//16-10-12 
  if len <> 0ul 
  then
    begin // at least one more block
      let l = min len (PRF.blocklen i) in 
      let cipher = Buffer.sub ciphertext 0ul l  in 
      let plain = Plain.sub plaintext 0ul l in 

      (*
      recall (PRF t.table); //16-09-22 could this be done by ! ??
      let s = PRF !t.table in
      let h = ST.get() in
      // WARNING: moving the PRF.find_otp outside the assume will segfault
      // at runtime, because t.table doesn't exist in real code
      assume(match PRF.find_otp #(PRF.State.rgn t) #i s x with
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

let live_2 #a0 #a1 h b0 b1 = Buffer.live #a0 h b0 /\ Buffer.live #a1 h b1 

val inv: h:mem -> #i:id -> #rw:rw -> e:state i rw -> Tot Type0
let inv h #i #rw e =
  match e with
  | State #i_ #rw_ #log_region log prf ->
    safeId i ==>
    ( let blocks = HS.sel h (PRF.State.table prf) in
      let entries = HS.sel h log in
      refines h i (PRF prf.mac_rgn) entries blocks )

(*
      // no need to be so specific here --- details follow from the invariant
      let c = Buffer.as_seq h1 (Buffer.sub ciphertext 0ul plainlen) in 
      let t: lbuffer 16 = Buffer.as_seq h1 (Buffer.sub ciphertext plainlen (Spec.taglen i)) in
      let a = Buffer.as_seq h1 aadtext in
      let l = field_encode i a c in (
      match PRF.find_0 (HS.sel h1 (PRF.State.table e.prf)) (PRF({iv=n; ctr=0ul})) with 
      | Some mac -> 
          let log = MAC.ilog (MAC.State.log mac) in 
          m_contains log h1 /\ m_sel h1 log == Some (l,t)
      | None -> False))
*)      

val encrypt: 
  i: id -> e:state i Writer -> 
  n: Cipher.iv (alg i) ->
  aadlen: UInt32.t {aadlen <=^ aadmax} -> 
  aadtext: lbuffer (v aadlen) -> 
  plainlen: UInt32.t {safelen i (v plainlen) 1ul} -> 
  plaintext: plainBuffer i (v plainlen) -> 
  ciphertext:lbuffer (v plainlen + v (Spec.taglen i)) 
  { Buffer.disjoint aadtext ciphertext /\
    Buffer.disjoint_2 (Plain.as_buffer plaintext) aadtext ciphertext }
  ->  STL unit
  (requires (fun h -> 
    inv h #i #Writer e /\
    live_2 h aadtext ciphertext /\ Plain.live h plaintext /\
    Buffer.disjoint aadtext ciphertext /\ //TODO add disjointness for plaintext
    (prf i ==> find (HS.sel h e.log) n == None) // The nonce must be fresh!
      ))
  (ensures (fun h0 _ h1 -> 
    //TODO some "heterogeneous" modifies that also records updates to logs and tables
    Buffer.modifies_1 ciphertext h0 h1 /\ 
    live_2 h1 aadtext ciphertext /\ Plain.live h1 plaintext /\
    inv h1 #i #Writer e /\ 
    (safeId i ==> (
      let aad = Buffer.as_seq h1 aadtext in
      let p = Plain.sel_plain h1 plainlen plaintext in
      let c = Buffer.as_seq h1 ciphertext in
      HS.sel h1 e.log == SeqProperties.snoc (HS.sel h0 e.log) (Entry n aad (v plainlen) p c)))))

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
    live_2 h aadtext ciphertext /\ Plain.live h plaintext ))
  (ensures (fun h0 verified h1 -> 
    inv h1 #i #Reader e /\
    live_2 h1 aadtext ciphertext /\ Plain.live h1 plaintext /\
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

let encrypt i st n aadlen aad plainlen plain cipher_tagged =
  push_frame();
  let x = PRF({iv = n; ctr = 0ul}) in // PRF index to the first block
  let ak = PRF.prf_mac i st.prf x in  // used for keying the one-time MAC
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in 
  let tag = Buffer.sub cipher_tagged plainlen (Spec.taglen i) in 

  assume false; //16-10-04 
  counter_enxor i st.prf (PRF.incr i x) plainlen plain cipher;
  
  // Compute MAC over additional data and ciphertext
  let l, acc = accumulate ak aadlen aad plainlen cipher in 
  MAC.mac ak l acc tag;
  pop_frame()


let decrypt i st iv aadlen aad plainlen plain cipher_tagged =
  push_frame();
  let x = PRF({iv = iv; ctr = 0ul}) in // PRF index to the first block
  let ak = PRF.prf_mac i st.prf x in   // used for keying the one-time MAC
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in 
  let tag = Buffer.sub cipher_tagged plainlen (Spec.taglen i) in 

  // First recompute and check the MAC
  let h0 = ST.get() in
  assume(
    MAC(Buffer.live h0 ak.r /\ norm h0 ak.r) /\
    Buffer.live h0 aad /\ Buffer.live h0 cipher);

  let l, acc = accumulate ak aadlen aad plainlen cipher in

  let h = ST.get() in 
  assert(mac_log ==> l = encode_both aadlen (Buffer.as_seq h aad) plainlen (Buffer.as_seq h cipher));

  let verified = MAC.verify ak l acc tag in

  // let h1 = ST.get() in
  // assert(mac_log /\ MAC.authId (i,iv) ==> (verified == (HS.sel h1 (MAC(ilog ak)) = Some (l,tag))));  

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
