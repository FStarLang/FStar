module Crypto.AEAD.Chacha20Poly1305.Ideal 

// We implement ideal AEAD on top of ideal Chacha20 and ideal Poly1305. 
// We precisely relate AEAD's log to their underlying state.

// This file intends to match the spec of AEAD0.fst in mitls-fstar. 

open FStar.HST
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.HST.Monotonic.RRef

open Crypto.Symmetric.Bytes
open Plain

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module Spec = Crypto.Symmetric.Poly1305.Spec
module MAC = Crypto.Symmetric.Poly1305.MAC

module Block = Crypto.Symmetric.BlockCipher
module PRF = Crypto.Symmetric.Chacha20.PRF

type region = rgn:HH.rid {HS.is_eternal_region rgn}

let ctr x = PRF(x.ctr)

let alg (i:id) = Block.CHACHA20 //16-10-02  temporary

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
type adata = b:bytes { Seq.length b < 2000 } 
type cipher (i:id) (l:nat) = lbytes(l + v (Spec.taglen i))

// Should be n:UInt128.t{n < pow2 96}
type iv (i:id) = lbuffer 12 // its computation from siv is left to the next level for now

noeq type entry (i:id) =
  | Entry: 
      nonce:Block.iv (alg i) -> 
      ad:adata -> 
      l:plainLen -> 
      p:plain i l -> 
      c:cipher i (Seq.length (repr #i #l p)) -> 
      entry i

type rw = | Reader | Writer 

noeq type state (i:id) (rw:rw) =
  | State:
      #region: rgn (* no need for readers? *) ->
      #log_region: rgn {if rw = Writer then region = log_region else HyperHeap.disjoint region log_region} ->
      log: HS.ref (Seq.seq (entry i)) {HS.frameOf log == log_region} ->
      prf: PRF.state i (* including its key *) ->
      state i rw


//16-09-18 where is it in the libraries?
private let min (a:u32) (b:u32) = if a <=^ b then a else b
private let minNat (a:nat) (b:nat) : nat = if a <= b then a else b

let gen i rgn = 
  let log = ralloc rgn (Seq.createEmpty #(entry i)) in
  let prf = PRF.gen rgn i in 
  State #i #Writer #rgn #rgn log prf

// let genReader #i #rgn (state i Writer) = ()
// no need for state? 


// MAC ENCODING from Chacha20Poly1305.fst

(* If the length is not a multiple of 16, pad to 16 *)
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
  | Block.CHACHA20 -> Crypto.Symmetric.Poly1305.Spec.elem
  | Block.AES256   -> lbytes (v Crypto.Symmetric.GF128.len) // not there yet
  
// val encode_bytes: i:id -> len:UInt32 -> b:lbytes (v len) -> Tot (Seq.seq (field i))

private let field_encode i aad cipher : Tot (Seq.seq (field i)) = 
  //TODO
  Seq.createEmpty

//16-09-18 how to get <- syntax?
open FStar.HyperStack

private val add_bytes:
  #i: MAC.id ->
  st: MAC.state i ->
  l0: MAC.itext -> 
  a : MAC.accB i ->
  len: UInt32.t ->
  txt:lbuffer (v len) -> STL MAC.itext
  (requires (fun h -> 
    Buffer.live h txt /\ MAC.acc_inv st l0 a h))
  (ensures (fun h0 l1 h1 -> 
    Buffer.modifies_1 a h0 h1 /\ 
    Buffer.live h1 txt /\ 
//?    (MAC.ideal ==> l1 = MAC.encode_pad l0 (MAC.sel_bytes h0 txt)) /\
    MAC.acc_inv st l1 a h1))

let rec add_bytes #i st log a len txt =
  assume false; //TODO
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

// will require StackInline for the accumulator 
private let accumulate i ak aadlen aad plainlen cipher = 
  let acc = MAC.start ak in
  let l = MAC.text_0 in 
  let l = add_bytes ak l acc aadlen aad in
  let l = add_bytes ak l acc plainlen cipher in 
  let l = 
    let final_word = Buffer.create 0uy 16ul in 
    store_uint32 4ul (Buffer.sub final_word 0ul 4ul) aadlen;
    store_uint32 4ul (Buffer.sub final_word 8ul 4ul) plainlen;
    MAC.add ak l acc final_word in
  l, acc


// INVARIANT (WIP)

let maxplain (i:id) = pow2 14 // for instance
private let safelen (i:id) (l:nat) (c:UInt32.t{0ul <^ c /\ c <=^ PRF.maxCtr }) = 
  l = 0 \/ (
    let bl = v (Block( blocklen (alg i))) in
    FStar.Mul(
      l + (v (c -^ 1ul)) * bl <= maxplain i /\ 
      l  <= v (PRF.maxCtr -^ c) * bl ))
    
// Computes PRF table contents for countermode encryption of 'plain' to 'cipher' starting from 'x'.
val counterblocks: 
  i:id -> rgn:region -> 
  x:PRF.domain {ctr x >^ 0ul} -> 
  l:nat {safelen i l (ctr x)} -> 
  plain:Plain.plain i l -> 
  cipher:lbytes l -> 
  Tot (Seq.seq (PRF.entry rgn i)) // each entry e {PRF(e.x.id = x.iv /\ e.x.ctr >= ctr x)}
  (decreases l)
  
let rec counterblocks i rgn x l plain cipher = 
  let blockl = v (Block(blocklen (alg i))) in 
  if l = 0 
  then Seq.createEmpty
  else 
    let l0 = minNat l blockl in 
    let l_32 = UInt32.uint_to_t l0 in 
    let block = PRF.Entry x (PRF.OTP l_32 (Plain.slice plain 0 l0) (Seq.slice cipher 0 l0)) in
    let cipher: lbytes(l - l0) = Seq.slice cipher l0 l in
    let plain = Plain.slice plain l0 l in
    // assert(safelen i (l - l0) (PRF(x.ctr +^ 1ul)));
    let blocks = counterblocks i rgn (PRF.incr x) (l - l0) plain cipher in
    SeqProperties.cons block blocks

(*
// checks PRF table contents against AEAD entries
val refines: 
  h:mem -> 
  i:id {authId i } -> rgn:region ->
  entries: Seq.seq (entry i) -> 
  blocks: Seq.seq (PRF.entry rgn i) -> Tot Type
  (decreases (Seq.length entries))

#reset-options "--print_universes"
let rec refines h i rgn entries blocks = 
  if Seq.length entries = 0 then 
    Seq.length blocks == 0
  else
  (match Seq.index entries 0 with
  | Entry nonce ad l plain cipher_tagged -> 
    begin
      let bl = v (Block( blocklen (alg i))) in
      let b = (l + bl -1) / bl in // number of blocks XOR-ed for this encryption
      (b < Seq.length blocks /\
      (match Seq.index blocks 0 with
      | PRF.Entry x e -> 
          let m:MAC.state (i, nonce) = e in
          let xors    = Seq.slice blocks 1 (b+1)  in 
          let blocks  = Seq.slice blocks (b+2) (Seq.length blocks - b - 2) in 
          let entries = Seq.slice entries 1 (Seq.length entries) in 
          let cipher, tag = SeqProperties.split cipher_tagged l in
          (x = PRF({iv=nonce; ctr=0ul}) /\
          xors = counterblocks i rgn (PRF.incr x) l plain cipher /\
          (match sel h (MAC.State.log m) with
          | None           -> False
          | Some (msg,tag) -> msg == field_encode i ad plain /\ refines h i rgn entries blocks))))
    end)
*)

(*
let lookupIV (i:id) (s:Seq.seq (entry i)) = Seq.seq_find (fun e:entry i -> e.iv = iv) s // <- requires iv:UInt128.t
*)
 


// COUNTER_MODE LOOP from Chacha20 

let ctr_inv ctr len = 
  len =^ 0ul \/
  ( 0ul <^ ctr /\
    v ctr + v(len /^ PRF.blocklen) < v PRF.maxCtr)  //we use v... to avoid ^+ overflow

// XOR-based encryption and decryption (just swap ciphertext and plaintext)
val counter_enxor: 
  i:id -> t:PRF.state i -> x:PRF.domain -> len:u32{ctr_inv (PRF x.ctr) len} ->
  plaintext:plainBuffer i (v len) -> 
  ciphertext:lbuffer (v len) {
    Buffer.disjoint (PRF t.key) ciphertext /\
    Buffer.disjoint (bufferT plaintext) (PRF t.key) /\
    Buffer.disjoint (bufferT plaintext) ciphertext /\ 
    Buffer.frameOf (bufferT plaintext) <> (PRF t.rgn)
    } -> 
  STL unit
    (requires (fun h -> 
      Buffer.live h ciphertext /\ 
      Buffer.live h (PRF t.key) /\ 
      Plain.live h plaintext ))
    (ensures (fun h0 _ h1 -> 
      // Buffer.live h1 ciphertext /\ 
      // Buffer.modifies_1 ciphertext h0 h1 /\ //16-09-22  We miss a hybrid modifies including PRF(t.table) 
      True
    ))
// this only touches buffers.
val counter_dexor: 
  i:id -> t:PRF.state i -> x:PRF.domain -> len:u32{ctr_inv (PRF x.ctr) len} ->
  plaintext:plainBuffer i (v len) -> 
  ciphertext:lbuffer (v len) {
    Buffer.disjoint (bufferT plaintext) ciphertext /\ 
    Buffer.frameOf (bufferT plaintext) <> PRF t.rgn } -> 
  STL unit
    (requires (fun h -> Buffer.live h ciphertext /\ Buffer.live h (PRF t.key) /\ Plain.live h plaintext))
    (ensures (fun h0 _ h1 -> let b = bufferT plaintext in Buffer.live h1 b /\ Buffer.modifies_1 b h0 h1))

let rec counter_dexor i t x len plaintext ciphertext =
  if len <> 0ul 
  then
    begin // at least one more block

      assume false;//16-10-02 
      
      let l = min len PRF.blocklen in 
      let cipher = Buffer.sub ciphertext 0ul l  in 
      let plain = Plain.sub plaintext 0ul l in 

      recall (PRF t.table); //16-09-22 could this be done by ! ??
      let s = PRF.find_1 (PRF !t.table) x in 
      let h = HST.get() in 
      assume(match s with | Some (PRF.OTP l' p c) -> l == l' /\ c = sel_bytes h l cipher | None -> False);

      PRF.prf_dexor i t x l plain cipher;

      let len = len -^ l in 
      let ciphertext = Buffer.sub ciphertext l len in
      let plaintext = Plain.sub plaintext l len in
      counter_dexor i t (PRF.incr x) len plaintext ciphertext
    end

let rec counter_enxor i t x len plaintext ciphertext =
  if len <> 0ul 
  then
    begin // at least one more block

      assume false;//16-10-02 

      let l = min len PRF.blocklen in 
      let cipher = Buffer.sub ciphertext 0ul l in 
      let plain = Plain.sub plaintext 0ul l in 

      recall (PRF t.table); //16-09-22 could this be done by ! ??
      let s = (PRF !t.table) in 
      assume(is_None(PRF.find_1 s  x)); 
      PRF.prf_enxor i t x l cipher plain;

      let len = len -^ l in 
      let ciphertext = Buffer.sub ciphertext l len in
      let plaintext = Plain.sub plaintext l len in
      counter_enxor i t (PRF.incr x) len plaintext ciphertext
    end

// ENCRYPT AND DECRYPT
// some code duplication, but in different typing contexts
//16-09-18 not yet using ideal state.

(*
val encrypt: 
  i:id -> e:state i Writer -> n:Block.iv (alg i) ->
  aadlen:UInt32.t -> aadtext:lbuffer (v aadlen) -> 
  plainlen:UInt32.t -> plaintext:plainBuffer i (v plainlen) -> 
  ciphertext:lbuffer (v plainlen + v (Spec.taglen i)) ->
  STL unit
  (requires (fun h -> 
    Buffer.live h aadtext /\ Plain.live h plaintext /\ Buffer.live h ciphertext /\
    //TODO: add disjointness
    //TODO add invariant /\ n not in the table yet. 
    (authId i ==> PRF.find_0 (HS.sel h (PRF.State.table e.prf)) (PRF({iv=n; ctr=0ul})) == None)
    ))
  (ensures (fun h0 _ h1 -> 
    //TODO some "heterogeneous" modifies that also records updates to logs and tables
    Buffer.modifies_1 ciphertext h0 h1 /\ 
    Buffer.live h1 ciphertext /\ 
    Buffer.live h1 aadtext /\
    Plain.live h1 plaintext /\
    (MAC.ideal /\ authId i ==> (
      let c = Buffer.as_seq h1 (Buffer.sub ciphertext 0ul plainlen) in 
      let t: lbuffer 16 = Buffer.as_seq h1 (Buffer.sub ciphertext plainlen (Spec.taglen i)) in
      let a = Buffer.as_seq h1 aadtext in
      let l = field_encode i a c in (
      match PRF.find_0 (HS.sel h1 (PRF.State.table e.prf)) (PRF({iv=n; ctr=0ul})) with 
      | Some mac -> 
          let log = MAC.ilog (MAC.State.log mac) in 
          m_contains log h1 /\ m_sel h1 log == Some (l,t)
      | None -> False))
    )))
*)

let encrypt i st n aadlen aad plainlen plain cipher_tagged =
  push_frame();
  let x = PRF({iv = n; ctr = 0ul}) in // PRF index to the first block
  let ak = PRF.prf_mac i st.prf x in     // used for keying the one-time MAC
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in 
  let tag = Buffer.sub cipher_tagged plainlen (Spec.taglen i) in 
  counter_enxor i st.prf (PRF.incr x) plainlen plain cipher;
  
  // Compute MAC over additional data and ciphertext
  let l, acc = accumulate i ak aadlen aad plainlen cipher in 
  MAC.mac ak l acc tag;
  pop_frame()


(*
val decrypt: 
  i:id -> e:state i -> iv:UInt64.t -> 
  aadlen:UInt32.t -> aadtext:lbytes (v aadlen) -> 
  plainlen:UInt32.t -> plaintext:lbytes (v plainlen) -> 
  ciphertext:lbytes (v plainlen) -> tag:MAC.tagB -> 
  STL UInt32.t
  (requires (fun h -> 
    live h key /\ live h aadtext /\ live h plaintext /\ 
    live h ciphertext /\ live h tag ))
  (ensures (fun h0 _ h1 -> 
    modifies_1 plaintext h0 h1 /\ 
    live h1 plaintext))
*)

let decrypt i st iv aadlen aad plainlen plain cipher_tagged =
  push_frame();
  let x = PRF({iv = iv; ctr = 0ul}) in // PRF index to the first block
  let ak = PRF.prf_mac i st.prf x in     // used for keying the one-time MAC
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in 
  let tag    = Buffer.sub cipher_tagged plainlen (Spec.taglen i) in 

  // First recompute and check the MAC
  let l, acc = accumulate i ak aadlen aad plainlen cipher in
  let verified  = MAC.verify ak l acc tag in 

  if verified then counter_dexor i st.prf (PRF.incr x) plainlen plain cipher;
  pop_frame();

  if verified then 0ul else 1ul //TODO pick and enforce error convention.
