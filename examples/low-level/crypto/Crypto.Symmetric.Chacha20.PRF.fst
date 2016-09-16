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

open FStar.HyperHeap
open FStar.HyperStack
open FStar.HST
open FStar.Ghost
open FStar.UInt8
open FStar.UInt32
open FStar.HST.Monotonic.RRef

open Plain // including its unrelated library stuff

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module MAC   = Crypto.Symmetric.Poly1305.MAC
module Block = Crypto.Symmetric.Chacha20


// LIBRARY STUFF 

let u8  = UInt8.t
let u32 = UInt32.t
let u64 = UInt64.t

(*
type bytes = Seq.seq UInt8.t 
type buffer = Buffer.buffer UInt8.t 

type lbytes (l:nat)  = b:bytes  {Seq.length b = l}
type lbuffer (l:nat) = b:buffer {Buffer.length b = l}

//TODO add functional correctness
assume val load_bytes: l:UInt32.t -> buf:lbuffer(v l) -> STL (lbytes(v l))
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 r h1 -> h0 == h1))
assume val store_bytes: l:UInt32.t -> buf:lbuffer(v l) -> lbytes(v l) -> ST unit
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 r h1 -> live h1 buf /\ modifies_1 buf h0 h1))
*)

assume val random: n:nat -> ST (lbytes n) 
  (requires (fun m -> True))
  (ensures  (fun m0 _ m1 -> modifies Set.empty m0 m1))


// PRF TABLE 

type domain = { iv:u64; ctr:u32 } // could move to concrete CHACHA20
let incr (x:domain {x.ctr <^ 1000ul})  = { iv = x.iv; ctr = x.ctr +^ 1ul }

let block = b:bytes {Seq.length b = v Block.blocklen}

// the range of our PRF, after idealization and "reverse inlining."
// for 1TPs, we keep both the plain and cipher blocks, instead of their XOR.

noeq type otp i = | OTP: l:nat -> plain i l -> cipher:bytes{Seq.length cipher = l} -> otp i

let range (rgn: HH.rid) (i:id) (x:domain): Type0 = 
  if x.ctr = 0ul 
  then m:MAC.state (i,x.iv) {MAC.State.region m = rgn} 
  else otp i

noeq type entry (rgn: HH.rid) (i:id) = | Entry: x:domain -> range:range rgn i x -> entry rgn i 


let find (#rgn: HH.rid) (#i:id) (s:Seq.seq (entry rgn i)) (x:domain) : option (range rgn i x) = 
  match SeqProperties.seq_find (fun (e:entry rgn i) -> e.x = x) s with 
  | Some e -> Some e.range 
  | None   -> None

// the PRF instance, including its key and memoization table
// TODO separate on rw, with multiple readers? 
noeq type state (i:id) = 
  | State: #rgn: HH.rid {is_eternal_region rgn} ->
           key:lbuffer (v Block.keylen) -> 
           table:FStar.HyperStack.ref (Seq.seq (entry rgn i)) -> state i // should be maybe_mrref; for later. 


val gen: rgn: HH.rid {is_eternal_region rgn} -> i:id -> ST (state i)
  (requires (fun h -> True))
  (ensures  (fun h0 s h1 -> sel h1 s.table == Seq.createEmpty #(entry rgn i)))

let gen rgn i =
  let key = Buffer.rcreate rgn 0uy Block.keylen in
  store_bytes Block.keylen key (random 32);
  let table = ralloc rgn (Seq.createEmpty #(entry rgn i)) in
  State #i #rgn key table


// computes a PRF block and copies its len first bytes to output
private let getBlock i t x len (output:lbuffer (v len)) = 
  Block.chacha20 output t.key x.iv x.ctr Block.constant len


// We encapsulate the 3 usages of the PRF in specific functions.
// But we still use a single, ctr-dependent range in the table. 
//
// For xor-based encryption, 
// the ideal variant records both the plaintext and the ciphertext
// whereas the real PRF output is their xor.

// the first block (ctr=0) is used to generate a single-use MAC
val prf_mac: i:id -> t:state i -> x:domain -> ST (MAC.state (i,x.iv))
  (requires (fun h0 -> x.ctr = 0ul))
  (ensures (fun h0 mac h1 -> 
    match find (sel h1 t.table) x with 
    | Some (mac: MAC.state (i,x.iv)) -> MAC.genPost (i,x.iv) t.rgn h0 mac h1
    | None     -> False
    // we guarantee the stateful post of MAC.create when x is not in the table. 
    // in all cases, we return the state in the table
  ))
 
// generates a fresh block for x and XORs it with plaintext
val prf_enxor: i:id -> t:state i -> x:domain -> 
  l:u32 {l <^ Block.blocklen} -> plain:plainBuffer i (v l) -> cipher:lbuffer (v l) -> STL unit 
  (requires (fun h0 -> 
     x.ctr <> 0ul /\ Plain.live h0 plain /\ live h0 cipher /\
     is_None(find (sel h0 t.table) x) 
     ))
  (ensures (fun h0 _ h1 -> 
     modifies_1 cipher h0 h1 /\
     (match find (sel h1 t.table) x with 
     | Some (p,c) -> p = sel_bytes h1 plain /\ c = sel_bytes h1 cipher 
     | None -> False 
     )))

// reuse the same block for x and XORs it with ciphertext
val prf_dexor: i:id -> t:state i -> x:domain -> 
  l:u32 {l <^ Block.blocklen} -> plain:plainBuffer i (v l) -> cipher:lbuffer (v l) -> STL unit 
  (requires (fun h0 -> 
     x.ctr <> 0ul /\ Plain.live h0 plain /\ live h0 cipher /\
     (match find (sel h0 t.table) x with 
     | None -> False
     | Some (p,c) -> c == sel_bytes h0 cipher
     )))
  (ensures (fun h0 _ h1 -> 
     modifies_1 plain h0 h1 /\
     (match find (sel h1 t.table) x with 
     | Some (p,c) -> p == sel_bytes h1 plain 
     | None -> False 
     )))

// it would be nicer to share the ideal find/memoization across the 3 functions

let prf_mac i t x = 
  if authId i then (
    match find !t.table x with 
    | Some mac -> mac 
    | None     -> (let mac = MAC.gen (i,x.iv) t.rgn in 
                 t.table := SeqProperties.snoc (Entry x mac) !t.table;
                 mac ))
  else (
    let keyBytes = create 0uy Block.keylen in 
    getBlock t x Block.keylen keyBytes;
    MAC.coerce i t.rgn keyBytes )

let prf_enxor i t x l output input = 
  if authId i then (
    let c = random l in   
    store_bytes l output c;
    t.table := SeqProperties.snoc (Entry x (load_bytes l input,c)) !t.table )
  else (
    getBlock t x l output;
    Buffer.Utils.xor_bytes_inplace output input l ) 

let prf_dexor i t x l output input = 
  if authId i then ( 
    match find !t.table x with 
    | Some (p,c) -> Plain.store l output p)
  else (
    getBlock t x l output; 
    Buffer.Utils.xor_bytes_inplace output input l )
