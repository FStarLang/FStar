module Crypto.AEAD.Chacha20Poly1305.Ideal 

// We implement ideal AEAD on top of ideal Chacha20 and ideal Poly1305. 
// We precisely relate AEAD's log to their underlying state.

// This file intends to match the spec of AEAD0.fst in mitls-fstar. 

open FStar.HST
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
// open Crypto.Symmetric.Chacha20

module Spec = Crypto.Symmetric.Poly1305.Spec
module MAC = Crypto.Symmetric.Poly1305.MAC
module PRF = Crypto.Symmetric.Chacha20.PRF

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


(*** representations ***)

// LOW-LEVEL? We use high-level (immutable) bytes for convenience, but
// we try to remain compatible with stack-based implementations, 

type bytes = Seq.seq UInt8.t 
type buffer = Buffer.buffer UInt8.t 

type lbuffer (l:nat) = b:buffer {Buffer.length b = l}
type lbytes (l:nat)  = b:bytes  {Bytes.length b = l}

//TODO add functional correctness
assume val load_bytes: l:UInt32.t -> buf:buffer {v l <= Buffer.length b} -> STL (lbytes(v l))
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 r h1) -> h0 = h1) 
assume val save_bytes: l:UInt32.t -> buf:buffer {v l = Buffer.length b} -> lbytes(v l) -> ST unit
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 r h1 -> live h1 b /\ modifies_1 buf h0 h1))
    
let tagLen (i:id) = 16ul // to be generalized
type tagB i = b:lbuffer { v(tagLen i) }

// Placeholders for plaintexts and additional data, represented as bounded bytestrings.
type plainLen = n:nat { n < 1000 } 
assume type plain (i:id) (l:plainLen) 
assume val repr: #i:id -> #l:plainLen -> p:plain i l -> Tot (b:bytes {Seq.length b = l})
type adata = b:bytes { Seq.length b < 2000 } 

type iv i = UInt64.t // its computation from siv is left to the next level for now 

type entry (i:id) =
  | Entry: 
      nonce:iv i -> ad:adata i -> 
      l:plainLen -> p:plain i l -> c:cipher i (length (repr p)) -> 
      entry i

type rw = | Reader | Writer 
type state (i:id) (rw:rw) = 
  | State:
      #region: rgn (* not needed for readers? *) ->
      #log_region: rgn {if rw = Writer then region = log_region else HyperHeap.disjoint region log_region}
      log: rref log_region (Seq.seq (entry i)) -> 
      prf: PRF.state (* including its key *) ->
      state i rw

(*** invariant ***)

// Computes PRF table contents for countermode encryption of 'plain' to 'cipher' starting from 'x'.
val counterblocks: 
   x:PRF.domain { x.ctr >^ 0ul } -> 
   plain:bytesT -> cipher:bytesT { Seq.length plain = Seq.length cipher } -> 
  Tot (Seq.seq PRF.Entry)

let rec counterblocks x plain cipher = 
  let l = Seq.length plain in 
  if l then Seq.empty
  else 
    let l0 = min l blockLen in 
    let block = PRF.Entry x (Seq.slice 0 l0 plain, Seq.slice 0 l0 cipher) in
    Seq.cons block (counterblocks { nonce = x.nonce; ctr = x.ctr +^ 1ul } (Seq.slice l0 l plain) (Seq.slice l0 l cipher)

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

val encrypt: 
  i:id -> e:state i Writer -> iv:UInt64.t 
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

// #reset-options "--z3timeout 100"
// still failing below 

let chacha20_aead_encrypt key iv constant aadlen aadtext plainlen plaintext ciphertext tag =
  push_frame();
  (* Create OTK, using first block of Chacha20 *)
  let otk  = create 0uy 32ul in 
  let counter = 0ul in 
  chacha20 otk key iv counter constant 32ul;

  (* Encrypt the plaintext, using Chacha20, counter at 1 *)
  let counter = 1ul in
  counter_mode key iv counter constant plainlen plaintext ciphertext;
 
  (* Initialize MAC algorithm with one time key *)
  (* encapsulate (r,s) and a; we should probably clear otk *)
  let ak = MAC.coerce MAC.someId HyperHeap.root otk in 
  let acc = MAC.start ak in

  (* Compute MAC over additional data and ciphertext *)
  let l = MAC.text_0 in 
  let l = add_bytes ak l acc aadlen aadtext in
  let l = add_bytes ak l acc plainlen ciphertext in 
  let l = 
    let final_word = create 0uy 16ul in 
    length_word final_word aadlen plainlen;
    MAC.add ak l acc final_word in
  MAC.mac ak l acc tag;
  pop_frame()

let chacha20_aead_decrypt key iv constant aadlen aadtext plainlen plaintext ciphertext tag =
  push_frame();
  (* Create OTK, using first block of Chacha20 *)
  let otk = create 0uy 32ul in 
  let counter = 0ul in 
  chacha20 otk key iv counter constant 32ul;

  (* Initialize MAC algorithm with one time key *)
  (* encapsulate (r,s) and a; we should probably clear otk *)
  let ak = MAC.coerce MAC.someId HyperHeap.root otk in 
  let acc = MAC.start ak in

  (* First recompute and check the MAC *)
  let l = MAC.text_0 in 
  let l = add_bytes ak l acc aadlen aadtext in
  let l = add_bytes ak l acc plainlen ciphertext in 
  let l = 
    let final_word = create 0uy 16ul in 
    length_word final_word aadlen plainlen;
    MAC.add ak l acc final_word in
  let verified  = MAC.verify ak l acc tag in 
  
  if verified then
    begin (* decrypt; note plaintext and ciphertext are swapped. *) 
      let counter = 1ul in 
      counter_mode key iv counter constant plainlen ciphertext plaintext
    end;

  pop_frame();
  if verified then 0ul else 1ul //TODO pick and enforce error convention.

