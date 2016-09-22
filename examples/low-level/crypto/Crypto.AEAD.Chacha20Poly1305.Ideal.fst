module Crypto.AEAD.Chacha20Poly1305.Ideal 

// We implement ideal AEAD on top of ideal Chacha20 and ideal Poly1305. 
// We precisely relate AEAD's log to their underlying state.

// This file intends to match the spec of AEAD0.fst in mitls-fstar. 

open FStar.HST
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils

open Plain // including library stuff

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module Spec = Crypto.Symmetric.Poly1305.Spec
module MAC = Crypto.Symmetric.Poly1305.MAC

module PRF = Crypto.Symmetric.Chacha20.PRF
let ctr x = PRF(x.ctr)

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

type iv i = UInt64.t // its computation from siv is left to the next level for now 

noeq type entry (i:id) =
  | Entry: 
      nonce:iv i -> ad:adata -> 
      l:plainLen -> p:plain i l -> 
//16-09-18 strange error
//    c:cipher i (Seq.length (repr #i #l p)) -> 
      entry i

type rw = | Reader | Writer 
noeq type state (i:id) (rw:rw) = 
  | State:
      #region: rgn (* no need for readers? *) ->
      #log_region: rgn {if rw = Writer then region = log_region else HyperHeap.disjoint region log_region} ->
      log: HS.ref (* log_region *) (Seq.seq (entry i)) -> 
      prf: PRF.state i (* including its key *) ->
      state i rw



//16-09-18 where is it in the libraries?
let min (a:u32) (b:u32) = if a <=^ b then a else b

let gen i rgn = 
  let log = ralloc rgn (Seq.createEmpty #(entry i)) in
  let prf = PRF.gen rgn i in 
  State #i #Writer #rgn #rgn log prf

// let genReader #i #rgn (state i Writer) = ()
// no need for state? 

(*
// INVARIANT (WIP)

// Computes PRF table contents for countermode encryption of 'plain' to 'cipher' starting from 'x'.
val counterblocks: 
   x:PRF.domain { x.ctr >^ 0ul } -> 
   plain:bytes -> cipher:bytes { Seq.length plain = Seq.length cipher } -> 
  Tot (Seq.seq (PRF.entry rgn i)

let rec counterblocks x plain cipher = 
  let l = Seq.length plain in 
  if l then Seq.createEmpty
  else 
    let l0 = min l PRF.blocklen in 
    let block = PRF.Entry x (Seq.slice 0 l0 plain, Seq.slice 0 l0 cipher) in
    Seq.cons block (counterblocks (incr x) (Seq.slice l0 l plain) (Seq.slice l0 l cipher))

// checks PRF table contents against AEAD entries
val refines: h:_ -> i:id -> entries: Seq.seq (entry i) -> blocks: Seq.seq (PRF.entry i) -> Tot bool
let rec refines h i entries blocks = 
  if Seq.length entries = 0 
  then Seq.length blocks = 0 
  else match Seq.index 0 entries with
  | Entry nonce ad l plain cipher_tagged -> 
    begin
      let nb = (l +^ blockLen -^ 1ul) /^ blockLen in // number of blocks XOR-ed for this encryption
      b < Seq.length blocks 
      &&
      let (PRF.Entry x v) = Seq.index 0 blocks in
      let xors    = Seq.slice 1 (b+1) blocks in 
      let entries = Seq.slice 1 (Seq.length entries) in 
      let blocks  = Seq.slice (b+2) (Seq.length blocks - b - 2) in 
      let cipher, tag = Seq.split cipher_tagged (Seq.length plain) in
      x.nonce = nonce && 
      x.ctr = 0ul &&
      xors = counterblocks (incr x) plain cipher &&
      ( let m: MAC.state i = v in 
        match sel h m.log with 
        | None           -> false
        | Some (msg,tag) -> msg = encode_2 ad plain && refines h entries blocks ) &&
      refines h i entries blocks 
    end

let lookupIV (i:id) (s:Seq.seq (entry i)) = Seq.seq_find (fun e:entry i -> e.iv = iv) s
*)


// MAC ENCODING from Chacha20Poly1305.fst

(* If the length is not a multipile of 16, pad to 16 *)
val pad_16: b:lbuffer 16 -> len:UInt32.t { v len <= 16 } -> STL unit
  (requires (fun h -> Buffer.live h b))
  (ensures  (fun h0 _ h1 -> 
    Buffer.live h1 b /\ Buffer.modifies_1 b h0 h1
    //TODO: be more precise, e.g. implement an injective spec.
  )) 
let pad_16 b len =
  // if len =^ 0ul then () else 
  memset (Buffer.offset b len) 0uy (16ul -^ len)

let uint32_bytes v : Tot (u8 * u8 * u8 * u8)= 
  Int.Cast.uint32_to_uint8 v,
  Int.Cast.uint32_to_uint8 (v >>^ 8ul),
  Int.Cast.uint32_to_uint8 (v >>^ 16ul),
  Int.Cast.uint32_to_uint8 (v >>^ 24ul)

//16-09-18 how to get <- syntax?
open FStar.HyperStack
let upd_uint32 (b:lbuffer 4) x : STL unit
  (requires (fun h -> Buffer.live h b))
  (ensures  (fun h0 _ h1 -> Buffer.live h1 b /\ Buffer.modifies_1 b h0 h1)) =
  let v0,v1,v2,v3 = uint32_bytes x in 
  Buffer.upd b 0ul v0;
  Buffer.upd b 1ul v1;
  Buffer.upd b 2ul v2;
  Buffer.upd b 3ul v3

(* Serializes the two lengths into the final MAC word *)
private val length_word: b:lbuffer 16 -> aad_len:UInt32.t -> len:UInt32.t -> STL unit
  (requires (fun h -> Buffer.live h b))
  (ensures  (fun h0 _ h1 -> Buffer.live h1 b /\ Buffer.modifies_1 b h0 h1))
  // we'll similarly need an injective spec
let length_word b aad_len len =
  assume false; // not sure why this fails.
  upd_uint32 (Buffer.offset b  0ul) aad_len;
  upd_uint32 (Buffer.offset b  4ul) 0ul;
  upd_uint32 (Buffer.offset b  8ul) len;
  upd_uint32 (Buffer.offset b 12ul) 0ul

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
    length_word final_word aadlen plainlen;
    MAC.add ak l acc final_word in
  l, acc


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
  if len =^ 0ul then () 
  else
    begin // at least one more block
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
  if len =^ 0ul then () 
  else
    begin // at least one more block
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
  i:id -> e:state i Writer -> iv:UInt64.t ->
  aadlen:UInt32.t -> aadtext:lbytes (v aadlen) -> 
  plainlen:UInt32.t -> plaintext:plain i (v plainLen) -> 
  ciphertext:lbuffer (v plainlen) -> tag:MAC.tagB i -> 
  STL unit
  (requires (fun h -> 
    live h key /\ live h aadtext /\ live h plaintext /\ live h ciphertext /\ live h tag /\ 
    lookupIV (sel h log) = None
    ))
  (ensures (fun h0 _ h1 -> 
    //TODO some "heterogeneous" modifies that also records updates to logs and tables
    modifies_2 ciphertext tag h0 h1 /\ 
    live h1 ciphertext /\ live h1 tag /\
    sel h1 log = snoc (Entry iv aadtext plaintext ciphertext) (sel h0 log) 
    ))

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

let encrypt i st iv aadlen aad plainlen plain cipher_tagged =
  push_frame();
  let x = PRF({iv = iv; ctr = 0ul}) in // PRF index to the first block
  let ak = PRF.prf_mac i st.prf x in     // used for keying the one-time MAC
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in 
  let tag = Buffer.sub cipher_tagged plainlen (Spec.taglen i) in 
  counter_enxor i st.prf (PRF.incr x) plainlen plain cipher;
  
  // Compute MAC over additional data and ciphertext
  let l, acc = accumulate i ak aadlen aad plainlen cipher in 
  MAC.mac ak l acc tag;
  pop_frame()

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
