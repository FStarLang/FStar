module Crypto.Symmetric.Chacha20.PRF

(* This file models our idealization of CHACHA20 (and soon any other
   block cipher used only in forward mode, such as AES for GCM or CCM)
   as a PRF to build authenticated encryption. 

   It models (an ad hoc variant of) the PRF security assumption:

   It captures the 3 different uses of the PRF in this construction:
   to generate the one-time MAC key, to generate a one-time-pad for
   encryption, and to generate a one-time-pad for decryption. *)

// TODO erase bookkeeping when ideal
// TODO add conditional idealization
// TODO improve agility (more i:id) and also support AES 
// TODO add pre- to statically prevent counter overflows

open FStar.HST
open FStar.Ghost
open FStar.UInt8
open FStar.UInt32
open FStar.HST.Monotonic.RRef

open Plain // also including its unrelated library stuff

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module MAC   = Crypto.Symmetric.Poly1305.MAC
module Block = Crypto.Symmetric.Chacha20


// LIBRARY STUFF 

let u8  = UInt8.t
let u32 = UInt32.t
let u64 = UInt64.t

// see also MAC.random
assume val random: l:u32 -> ST (lbytes (v l)) 
  (requires (fun m -> True))
  (ensures  (fun m0 _ m1 -> HS.modifies Set.empty m0 m1))

let region = rgn:HH.rid {HS.is_eternal_region rgn}

// PRF TABLE 

type domain = { iv:u64; ctr:u32 } // could move to concrete CHACHA20
let incr (x:domain {x.ctr <^ 1000ul})  = { iv = x.iv; ctr = x.ctr +^ 1ul }

let block = b:bytes {Seq.length b = v Block.blocklen}

// the range of our PRF, after idealization and "reverse inlining."
// for one-time-pads, we keep both the plain and cipher blocks, instead of their XOR.

type smac (rgn: region) i x = mac: MAC.state (i,x.iv) { MAC.State.region mac = rgn }
noeq type otp i = | OTP: l:u32 {l <=^ Block.blocklen} -> plain i (v l) -> cipher:lbytes (v l) -> otp i

let range (rgn: region) (i:id) (x:domain): Type0 = 
  if x.ctr = 0ul 
  then smac rgn i x 
  else otp i

// explicit coercions
let macRange rgn i (x:domain{x.ctr = 0ul}) (v:range rgn i x) : smac rgn i x = v
let otpRange rgn i (x:domain{x.ctr <> 0ul}) (v:range rgn i x) : otp i        = v

noeq type entry (rgn: region) (i:id) = | Entry: x:domain -> range:range rgn i x -> entry rgn i 

let find (#rgn: region) (#i:id) (s:Seq.seq (entry rgn i)) (x:domain) : option (range rgn i x) = 
  match SeqProperties.seq_find (fun (e:entry rgn i) -> e.x = x) s with 
  | Some e -> Some e.range 
  | None   -> None

let find_0 #rgn #i s (x:domain{x.ctr=0ul}) = 
  match find s x with
  | Some v -> Some(macRange rgn i x v)
  | None   -> None
let find_1 #rgn #i s (x:domain{x.ctr<>0ul}) = 
  match find s x with
  | Some v -> Some(otpRange rgn i x v)
  | None   -> None

// the PRF instance, including its key and memoization table
// TODO separate on rw, with multiple readers? 
noeq type state (i:id) = 
  | State: #rgn: region ->
           key:lbuffer (v Block.keylen) -> 
           table:HS.ref (Seq.seq (entry rgn i)) -> state i // should be maybe_mrref; for later. 

// TODO coerce, leak, and eventually dynamic compromise.

val gen: rgn: region -> i:id -> ST (state i)
  (requires (fun h -> True))
  (ensures  (fun h0 s h1 -> HS.sel h1 s.table == Seq.createEmpty #(entry rgn i)))

let gen rgn i =
  let key = Buffer.rcreate rgn 0uy Block.keylen in
  store_bytes Block.keylen key (random Block.keylen);
  let table = ralloc rgn (Seq.createEmpty #(entry rgn i)) in
  State #i #rgn key table

// computes a PRF block and copies its len first bytes to output

private val getBlock: #i:id -> t:state i -> domain -> len:u32 {len <=^ Block.blocklen} -> output:lbuffer (v len) -> ST unit
  (requires (fun h0 -> Buffer.live h0 output))
  (ensures (fun h0 r h1 -> Buffer.live h1 output /\ modifies_1 output h0 h1 ))

let getBlock #i t x len output = 
  assume false;//TODO don't see how this fails.
  Block.chacha20 output t.key x.iv x.ctr Block.constant len

// We encapsulate our 3 usages of the PRF in specific functions.
// But we still use a single, ctr-dependent range in the table. 
//
// For xor-based encryption, 
// the ideal variant records both the plaintext and the ciphertext
// whereas the real PRF output is their xor.

 
// the first block (ctr=0) is used to generate a single-use MAC
val prf_mac: i:id -> t:state i -> x:domain{x.ctr = 0ul} -> ST (MAC.state (i,x.iv))
  (requires (fun h0 -> True))
  (ensures (fun h0 mac h1 -> 
    match find_0 (HS.sel h1 t.table) x with 
    | Some mac' -> mac == mac' /\ MAC.genPost (i,x.iv) t.rgn h0 mac h1
    | None      -> False
    // we guarantee the stateful post of MAC.create when x is not in the table. 
    // in all cases, we return the state in the table
  ))

// generates a fresh block for x and XORs it with plaintext
val prf_enxor: i:id -> t:state i -> x:domain{x.ctr <> 0ul} -> 
  l:u32 {l <=^ Block.blocklen} -> cipher:lbuffer (v l) -> plain:plainBuffer i (v l) -> ST unit 
  (requires (fun h0 -> 
     Plain.live h0 plain /\ Buffer.live h0 cipher /\ Buffer.disjoint (bufferT plain) cipher /\
     is_None(find_1 (HS.sel h0 t.table) x) 
     ))
  (ensures (fun h0 _ h1 -> 
     Plain.live h1 plain /\ Buffer.live h1 cipher /\
     modifies_1 cipher h0 h1 /\
     (match find_1 (HS.sel h1 t.table) x with 
     | Some (OTP l' p c) -> l = l' /\ p == sel_plain h1 l plain /\ c == sel_bytes h1 l cipher
     | None   -> False 
     )))

// reuse the same block for x and XORs it with ciphertext
val prf_dexor: i:id -> t:state i -> x:domain{x.ctr <> 0ul} -> 
  l:u32 {l <=^ Block.blocklen} -> plain:plainBuffer i (v l) -> cipher:lbuffer (v l) -> ST unit 
  (requires (fun h0 -> 
     Plain.live h0 plain /\ Buffer.live h0 cipher /\ Buffer.disjoint (bufferT plain) cipher /\
     (match find_1 (HS.sel h0 t.table) x with 
     | Some (OTP l' p c) -> l == l' /\ c == sel_bytes h0 l cipher
     | None -> False
     )))
  (ensures (fun h0 _ h1 -> 
     Plain.live h1 plain /\ Buffer.live h1 cipher /\
     // TODO modifies_1 plain h0 h1 /\
     (match find_1 (HS.sel h1 t.table) x with 
     | Some (OTP l' p c) -> l == l' /\ p == sel_plain h1 l plain
     | None -> False 
     )))

// it would be nicer to share the ideal find/memoization across the 3 functions

// can't get !t.table to work; isolated here. Why?
val read: i:id -> t:state i -> ST (Seq.seq (entry t.rgn i))
  (requires (fun h0 -> True))
  (ensures (fun h0 s h1 -> HS.sel h0 t.table == s))
let read i t = assume false; !t.table


let lemma_snoc_found (#rgn:region) (#i:id) (s:Seq.seq (entry rgn i)) (x:domain) (v:range rgn i x) : Lemma
  (requires (find s x == None))
  (ensures (find (SeqProperties.snoc s (Entry x v)) x == Some v))
  = ()  

#reset-options "--z3timeout 10000"

let prf_enxor i t x l cipher plain = 
  if authId i then (
    let p = Plain.load #i l plain in 
    let c = random l in // sample a fresh ciphertext block    
    store_bytes l cipher c; 
    let contents = read i t in 
    let newblock = OTP #i l p c in
    assume(find contents x == None); //TODO how to avoid explicit annotations on find_1 ?
    lemma_snoc_found contents x newblock; 
    t.table := SeqProperties.snoc contents (Entry x newblock))
  else (
    let plain = bufferRepr #i #(v l) plain in 
    getBlock t x l cipher;
    Buffer.Utils.xor_bytes_inplace cipher plain l ) 


let prf_dexor i t x l plain cipher = 
  if authId i then ( 
    let contents = read i t in
    match find_1 contents x with 
    | Some (OTP l' p c) -> Plain.store #i l plain p)
  else (
    let plain = bufferRepr #i #(v l) plain in 
    getBlock t x l plain; 
    Buffer.Utils.xor_bytes_inplace plain cipher l )

let prf_mac i t x = 
  if authId i then (
    let contents = read i t in //TODO unclear which pref is missing
    match find_0 contents x with 
    | Some mac -> mac 
    | None     -> (let mac = MAC.gen (i,x.iv) t.rgn in 
                 t.table := SeqProperties.snoc contents (Entry x mac);
                 mac ))
  else (
    let keyBytes = Buffer.rcreate t.rgn 0uy Block.keylen in 
    getBlock t x Block.keylen keyBytes;
    MAC.coerce (i,x.iv) t.rgn keyBytes )

