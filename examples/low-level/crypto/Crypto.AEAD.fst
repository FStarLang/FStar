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

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module Spec = Crypto.Symmetric.Poly1305.Spec
module MAC = Crypto.Symmetric.Poly1305.MAC

module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF

type region = rgn:HH.rid {HS.is_eternal_region rgn}

let ctr x = PRF(x.ctr)

let alg (i:id) = cipher_of_id i 

//16-10-12 TEMPORARY, while PRF remains somewhat CHACHA-specific
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

type rgn = rgn:HH.rid {HS.is_eternal_region rgn}
    
type tagB i = lbuffer ( v(Spec.taglen i))

// placeholder for additional data
let aadmax = 2000ul
type adata = b:bytes { Seq.length b <= v aadmax} 
type cipher (i:id) (l:nat) = lbytes(l + v (Spec.taglen i))


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
  State #i #Writer #rgn log prf


val coerce: i:id{~(prf i)} -> rgn:region -> key:lbuffer (v (PRF.keylen i)) -> ST (state i Writer)
  (requires (fun h -> Buffer.live h key))
  (ensures  (fun h0 st h1 -> True))
let coerce i rgn key = 
  let log = ralloc rgn (Seq.createEmpty #(entry i)) in // Shouldn't exist
  let prf = PRF.coerce rgn i key in
  State #i #Writer #rgn log prf


val genReader: #i:id -> st:state i Writer -> ST (state i Reader)
  (requires (fun _ -> True))
  (ensures  (fun _ _ _ -> True))
let genReader #i st =
  State #i #Reader #st.log_region st.log st.prf


// If the length is not a multiple of 16, pad to 16
// (we actually don't depend on the details of the padding)
val pad_16: b:lbuffer 16 -> len:UInt32.t { 0 < v len /\ v len <= 16 } -> STL unit
  (requires (fun h -> Buffer.live h b))
  (ensures  (fun h0 _ h1 -> 
    Buffer.live h0 b /\
    Buffer.live h1 b /\ 
    Buffer.modifies_1 b h0 h1 /\ 
    Seq.equal (Buffer.as_seq h1 b) (Seq.append (Buffer.as_seq h0 (Buffer.sub b 0ul len)) (Seq.create (16 - v len) 0uy)))) 
let pad_16 b len =
  memset (Buffer.offset b len) 0uy (16ul -^ len)

let field i = match alg i with 
  | Cipher.CHACHA20 -> Crypto.Symmetric.Poly1305.Spec.elem
  | Cipher.AES256   -> lbytes (v Crypto.Symmetric.GF128.len) // not there yet
  
// val encode_bytes: i:id -> len:UInt32 -> b:lbytes (v len) -> Tot (Seq.seq (field i))

private let field_encode i aad cipher : Tot (Seq.seq (field i)) = 
  //TODO
  Seq.createEmpty

open FStar.HyperStack

// add variable-length bytes to a MAC accumulator, one 16-byte word at a time
private val add_bytes:
  #i: MAC.id ->
  st: MAC.state i ->
  l0: MAC.itext -> 
  a : MAC.accB i ->
  len: UInt32.t ->
  txt:lbuffer (v len) -> STL MAC.itext
  (requires (fun h0 -> 
    Buffer.live h0 txt /\ MAC.acc_inv st l0 a h0))
  (ensures (fun h0 l1 h1 -> 
    Buffer.modifies_1 a h0 h1 /\ 
    Buffer.live h1 txt /\ MAC.acc_inv st l1 a h1 /\
    (mac_log ==> l1 = Spec.encode_bytes (Buffer.as_seq h1 txt))
    ))

let rec add_bytes #i st log a len txt =
  assume false; //TODO after specifying MAC.add
  push_frame();
  let r = 
    if len = 0ul then log
    else if len <^ 16ul then 
      begin
        let w = Buffer.create 0uy 16ul in
        Buffer.blit txt 0ul w 0ul len;
        pad_16 w len;
        MAC.add st log a w
      end
    else 
      begin
        let w = Buffer.sub txt 0ul 16ul in 
        let log = MAC.add st log a w in
        add_bytes st log a (len -^ 16ul) (Buffer.offset txt 16ul)
      end
  in
  pop_frame(); r

(*
private val accumulate: 
  #i: MAC.id -> ak: MAC.state i -> 
  aadlen:UInt32.t -> aad:lbuffer (v aadlen) ->
  plainlen:UInt32.t -> cipher:lbuffer (v plainlen) -> StackInline (MAC.itext * MAC.accB i)
  (requires (fun h0 -> 
    Buffer.live aad h0 /\ Buffer.live cipher h0))
  (ensures (fun h0 (l,a) h1 -> 
    Buffer.modifies_0 h0 h1 /\ // modified only freshly allocated buffers on the current stack
    MAC.acc_inv ak l a h1 /\
    (mac_log ==> reveal l = 
      Seq.snoc 
      (Seq.append (encode_bytes (Buffer.as_seq aad)) 
                  (encode_bytes (Buffer.as_seq cipher)))
      (encode_length aadlen plainlen))))
  // StackInline required for stack-allocated accumulator
*)
 
private let encode_lengths (aadlen:UInt32.t) (plainlen:UInt32.t) : b:lbytes 16
  { v aadlen = little_endian (Seq.slice b 0 4) /\
    v plainlen = little_endian (Seq.slice b 8 12) } = 
  let ba = uint32_bytes 4ul aadlen in
  let bp = uint32_bytes 4ul plainlen in 
  let open FStar.Seq in 
  let b = ba @| (Seq.create 4 0uy @| bp @| Seq.create 4 0uy) in
  //16-10-15 TODO SeqProperties?
  assume(ba = slice b 0 4);
  assume(bp = slice b 8 12);
  b

private let encode_both aadlen plainlen (aad:lbytes (v aadlen)) (plain:lbytes (v plainlen)) :
  e:Seq.seq Spec.elem {Seq.length e > 0 /\ SeqProperties.head e = Spec.encode(encode_lengths aadlen plainlen)} = 
  SeqProperties.cons (Spec.encode(encode_lengths aadlen plainlen))
    (Seq.append 
      (Spec.encode_bytes plain) 
      (Spec.encode_bytes aad))

private let lemma_encode_both al0 pl0 al1 pl1 
  (a0:lbytes(v al0)) (p0:lbytes(v pl0)) (a1:lbytes(v al1)) (p1:lbytes (v pl1)) : Lemma
  (requires encode_both al0 pl0 a0 p0 = encode_both al1 pl1 a1 p1)
  (ensures al0 = al1 /\ pl0 = pl1 /\ a0 = a1 /\ p0 = p1) = 

  let open FStar.Seq in 
  let open FStar.SeqProperties in
  let open Crypto.Symmetric.Poly1305.Spec in 
  let w0 = encode_lengths al0 pl0 in 
  let w1 = encode_lengths al1 pl1 in
  //assert(encode w0 = encode w1);
  lemma_encode_injective w0 w1; 
  //assert(al0 = al1 /\ pl0 = pl1);
  let ea0 = encode_bytes a0 in
  let ea1 = encode_bytes a1 in
  let ep0 = encode_bytes p0 in
  let ep1 = encode_bytes p1 in
  lemma_encode_length p0;
  lemma_encode_length p1;
  //assert(length ep0 = length ep1);
  //assert(encode_both al0 pl0 a0 p0 = cons (encode w0) (ep0 @| ea0));
  //assert(encode_both al1 pl1 a1 p1 = cons (encode w1) (ep1 @| ea1));
  lemma_append_inj (create 1 (encode w0)) (ep0 @| ea0) (create 1 (encode w1)) (ep1 @| ea1);
  //assert( ep0 @| ea0 = ep1 @| ea1);
  lemma_append_inj ep0 ea0 ep1 ea1;
  //assert(ep0 == ep1 /\ ea0 == ea1);
  lemma_encode_bytes_injective p0 p1;
  lemma_encode_bytes_injective a0 a1

(*
let rec map #a #b (f:a -> Tot b) (s:Seq.seq a) : Tot (Seq.seq b) (decreases (Seq.length s))= 
  if Seq.length s = 0 then Seq.createEmpty else
  SeqProperties.cons (f (SeqProperties.head s)) (map f (SeqProperties.tail s))

let lemma_map_injective_encoding s0 s1 : Lemma (map Spec.encode s0 = map Spec.encode s1 ==> s0 = s1) = ()
*)

private let accumulate i ak (aadlen:UInt32.t) (aad:lbuffer (v aadlen))
  (plainlen:UInt32.t) (cipher:lbuffer (v plainlen)) = 
  let acc = MAC.start ak in
  let l = MAC.text_0 in 
  let l = add_bytes ak l acc aadlen aad in
  let l = add_bytes ak l acc plainlen cipher in 
  let l = 
    let final_word = Buffer.create 0uy 16ul in 
    store_uint32 4ul (Buffer.sub final_word 0ul 4ul) aadlen;
    store_uint32 4ul (Buffer.sub final_word 8ul 4ul) plainlen;
    let h = ST.get() in 
    assert(encode_lengths aadlen plainlen = Buffer.as_seq h final_word);
    MAC.add ak l acc final_word in
  l, acc

// INVARIANT (WIP)

let maxplain (i:id) = pow2 14 // for instance

let safelen (i:id) (l:nat) (c:UInt32.t{0ul <^ c /\ c <=^ PRF.maxCtr i}) = 
  l = 0 || (
    let bl = v (Cipher( blocklen (alg i))) in
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
  let blockl = v (Cipher(blocklen (alg i))) in 
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
  let bl = v (Cipher( blocklen (alg i))) in
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
		     modifies_ref mac_rgn TSet.empty h h' /\
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
		    modifies_ref mac_rgn TSet.empty h h' /\
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

val all_above: #rgn:region -> #i:PRF.id -> s:Seq.seq (PRF.entry rgn i) -> domain i -> Tot bool (decreases (Seq.length s))
let rec all_above #rgn #i s x = 
  Seq.length s = 0 || ((SeqProperties.head s).x `above` x && all_above (SeqProperties.tail s) x )

// modifies a table (with entries above x) and a buffer.
let modifies_X_buffer_1 (#i:PRF.id) (t:PRF.state i) x b h0 h1 = 
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
    Seq.slice contents1 0 (Seq.length contents0) == contents0 /\
    all_above (Seq.slice contents1 (Seq.length contents0) (Seq.length contents1)) x
  else
    Buffer.modifies_1 b h0 h1)

val counter_enxor: 
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
    // if ciphertexts are authenticated, then fresh blocks are available
    (safeId i ==> (forall z. z `above` x ==> find_otp #t.mac_rgn #i (HS.sel h t.table) z == None))
    ))
  (ensures (fun h0 _ h1 -> 
    Plain.live h1 plain /\ 
    Buffer.live h1 cipher /\ 
    // in all cases, we extend the table only at x and its successors.
    modifies_X_buffer_1 t x cipher h0 h1 /\
    // if ciphertexts are authenticated, then we precisely know the table extension
    (safeId i ==> HS.sel h1 t.table ==
		  Seq.append (HS.sel h0 t.table) 
			     (counterblocks i t.mac_rgn x (v len) (Plain.sel_plain h1 len plain) (Buffer.as_seq h1 cipher)))
    // NB the post of prf_enxor should be strengthened a bit (using PRF.extends?)
    ))
    
let rec counter_enxor i t x len plain cipher =
  assume false;//16-10-12 
  if len <> 0ul then
    begin // at least one more block
      let l = min len (PRF.blocklen i) in 
      let cipher = Buffer.sub cipher 0ul l in 
      let plain = Plain.sub plain 0ul l in 
      (*
      recall (PRF t.table);
      let s = (PRF !t.table) in 
      assume(is_None(PRF.find s x));
      *)
      PRF.prf_enxor i t x l cipher plain;
      let len = len -^ l in 
      let cipher = Buffer.sub cipher l len in
      let plain = Plain.sub plain l len in
      counter_enxor i t (PRF.incr i x) len plain cipher
    end

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
    modifies_X_buffer_1 t x (as_buffer plain) h0 h1 /\
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
  ciphertext:lbuffer (v plainlen + v (Spec.taglen i)) ->
  STL unit
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
  ciphertext:lbuffer (v plainlen + v (Spec.taglen i)) -> STL bool
  (requires (fun h -> 
    inv h #i #Reader e /\
    live_2 h aadtext ciphertext /\ Plain.live h plaintext /\ 
    Buffer.disjoint aadtext ciphertext //TODO add disjointness for plaintext
    ))
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
  let l, acc = accumulate i ak aadlen aad plainlen cipher in 
  MAC.mac ak l acc tag;
  pop_frame()

let decrypt i st iv aadlen aad plainlen plain cipher_tagged =
  push_frame();
  let x = PRF({iv = iv; ctr = 0ul}) in // PRF index to the first block
  let ak = PRF.prf_mac i st.prf x in   // used for keying the one-time MAC
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in 
  let tag = Buffer.sub cipher_tagged plainlen (Spec.taglen i) in 

  assume false; //16-10-04

  // First recompute and check the MAC
  let l, acc = accumulate i ak aadlen aad plainlen cipher in
  let verified = MAC.verify ak l acc tag in
  if verified then counter_dexor i st.prf (PRF.incr i x) plainlen plain cipher;
  pop_frame();
  verified

