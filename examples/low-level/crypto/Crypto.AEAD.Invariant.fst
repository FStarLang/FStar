module Crypto.AEAD.Invariant
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

//module MAC = Crypto.Symmetric.Poly1305.MAC
module CMA = Crypto.Symmetric.UF1CMA

module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF

//16-09-18 where is it in the libraries??
let min (a:u32) (b:u32) = if a <=^ b then a else b
let minNat (a:nat) (b:nat) : nat = if a <= b then a else b

type region = rgn:HH.rid {HS.is_eternal_region rgn}

let ctr x = PRF(x.ctr)

//16-10-12 TEMPORARY, while PRF remains somewhat CHACHA-specific
//16-10-12 NB we are importing this restriction from Encoding too
//let id = i:id {i.cipher = CHACHA20_POLY1305}

noeq type entry (i:id) =
  | Entry: 
      nonce:Cipher.iv (alg i) -> 
      ad:adata -> 
      l:plainLen -> 
      p:plain i l -> 
      c:cipher i (Seq.length (as_bytes p)) -> 
      entry i

type rw = | Reader | Writer 

noeq type state (i:id) (rw:rw) =
  | State:
      #log_region: rgn -> // this is the *writer* region; the reader allocates nothing
      // the log should exist only when prf i
      log: HS.ref (Seq.seq (entry i)) {HS.frameOf log == log_region} ->
      // Was PRF(prf.rgn) == region. Do readers use its own PRF state?
      prf: PRF.state i {PRF(prf.rgn) == log_region} (* including its key *) ->
      ak: CMA.akey log_region i (* static, optional authentication key *) -> 
      state i rw

// INVARIANT (WIP)
 
let maxplain (i:id) = pow2 14 // for instance

// encryption loop invariant.
// l is the length of plaintext left to be encrypted; 
// c is the counter for encrypting the next block of plaintext.
let safelen (i:id) (l:nat) (c:UInt32.t{PRF.ctr_0 i <^ c /\ c <=^ PRF.maxCtr i}) = 
  l = 0 || (
    let bl = v (Cipher( blocklen (cipher_of_id i))) in
    FStar.Mul(
      l + (v (c -^ PRF.ctr_0 i -^ 1ul)) * bl <= maxplain i && 
      l  <= v (PRF.maxCtr i -^ c) * bl ))
    
// Computes PRF table contents for countermode encryption of 'plain' to 'cipher' starting from 'x'.
val counterblocks: 
  i:id {safeId i} -> 
  rgn:region ->  //the rgn is really superfluous, 
		//since it is only potentially relevant in the case of the mac, 
		//but that's always Seq.createEmpty here
                //16-10-13 but still needed in the result type, right?
  x:PRF.domain i{PRF.ctr_0 i <^ ctr x} -> 
  l:nat -> 
  from_pos:nat -> 
  to_pos:nat{from_pos <= to_pos /\ to_pos <= l /\ safelen i (to_pos - from_pos) (ctr x)} -> 
  plain:Plain.plain i l -> 
  cipher:lbytes l -> 
  Tot (Seq.seq (PRF.entry rgn i)) // each entry e {PRF(e.x.id = x.iv /\ e.x.ctr >= ctr x)}
  (decreases (to_pos - from_pos))
let rec counterblocks i rgn x l from_pos to_pos plain cipher = 
  let blockl = v (Cipher(blocklen (cipher_of_id i))) in 
  let remaining = to_pos - from_pos in 
  if remaining = 0 then
    Seq.createEmpty
  else 
    let l0 = minNat remaining blockl in 
    let l_32 = UInt32.uint_to_t l0 in 
    let plain_hd = Plain.slice plain from_pos (from_pos + l0) in
    let cipher_hd = Seq.slice cipher from_pos (from_pos + l0) in
    let block = PRF.Entry x (PRF.OTP l_32 plain_hd cipher_hd) in
    let blocks = counterblocks i rgn (PRF.incr i x) l (from_pos + l0) to_pos plain cipher in
    SeqProperties.cons block blocks

let num_blocks' (i:id) (l:nat) : Tot nat = 
  let bl = v (Cipher( blocklen (cipher_of_id i))) in
  (l + bl - 1) / bl

let num_blocks (#i:id) (e:entry i) : Tot nat = 
  let Entry nonce ad l plain cipher_tagged = e in
  num_blocks' i l
  
let refines_one_entry (#rgn:region) (#i:id{safeId i}) (h:mem) (e:entry i) (blocks:Seq.seq (PRF.entry rgn i)) = 
  let Entry nonce ad l plain cipher_tagged = e in
  let b = num_blocks e in 
  b + 1 = Seq.length blocks /\
  (let PRF.Entry x e = Seq.index blocks 0 in
   let xors = Seq.slice blocks 1 (b+1) in 
   let cipher, tag = SeqProperties.split cipher_tagged l in
   PRF (x.iv = nonce /\ x.ctr = PRF.ctr_0 i) /\ 
   safelen i l (PRF.ctr_0 i +^ 1ul) /\
   xors == counterblocks i rgn (PRF.incr i x) l 0 l plain cipher /\ //NS: forced to use propositional equality here, since this compares sequences of abstract plain texts. CF 16-10-13: annoying, but intuitively right?
   (let m = PRF.macRange rgn i x e in
    let mac_log = CMA.ilog (CMA.State.log m) in
    m_contains mac_log h /\ (
    match m_sel h (CMA.ilog (CMA.State.log m)) with
    | None           -> False
    | Some (msg,tag') -> msg = encode_both (FStar.UInt32.uint_to_t (Seq.length ad)) ad (FStar.UInt32.uint_to_t l) cipher /\
			tag = tag'))) //NS: adding this bit to relate the tag in the entries to the tag in that MAC log

// States consistency of the PRF table contents vs the AEAD entries
// (not a projection from one another because of allocated MACs and aad)
val refines: 
  h:mem -> 
  i:id {safeId i} -> rgn:region ->
  entries: Seq.seq (entry i) -> 
  blocks: Seq.seq (PRF.entry rgn i) -> GTot Type0
  (decreases (Seq.length entries))
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

open Crypto.Symmetric.PRF
let all_above (#rgn:region) (#i:id) (s:Seq.seq (PRF.entry rgn i)) (x:PRF.domain i) = 
  (forall (e:PRF.entry rgn i).{:pattern (s `SeqProperties.contains` e)} 
     s `SeqProperties.contains` e ==> e.x `PRF.above` x)

let modifies_table_above_x_and_buffer (#i:id) (#l:nat) (t:PRF.state i) 
				      (x:PRF.domain i) (b:lbuffer l)
				      (h0:HS.mem) (h1:HS.mem) = 
  Buffer.live h1 b /\ 
  (if prf i then 
    let r = PRF.itable i t in
    let rb = Buffer.frameOf b in 
    let rgns = Set.union (Set.singleton #HH.rid t.rgn) (Set.singleton #HH.rid rb) in 
    let contents0 = HS.sel h0 r in
    let contents1 = HS.sel h1 r in
    HS.modifies rgns h0 h1 /\ 
    HS.modifies_ref t.rgn (TSet.singleton (FStar.Heap.Ref (HS.as_ref r))) h0 h1 /\
    Buffer.modifies_buf_1 rb b h0 h1 /\
    Seq.length contents0 <= Seq.length contents1 /\
    Seq.equal (Seq.slice contents1 0 (Seq.length contents0)) contents0 /\
    all_above (Seq.slice contents1 (Seq.length contents0) (Seq.length contents1)) x
  else
    Buffer.modifies_1 b h0 h1)

let none_above (#i:id) (x:domain i) (t:PRF.state i) (h:mem) =
    safeId i ==> (forall (y:domain i{y `above` x}). find #t.mac_rgn #i (HS.sel h t.table) y == None)
