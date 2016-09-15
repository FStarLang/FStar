module Crypto.Symmetric.Chacha20.PRF

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.STH
open FStar.Set
open FStar.Int.Cast
open FStar.UInt8
open FStar.UInt32
open FStar.Seq
open FStar.Buffer

open MonotoneSeq
open FStar.HST.Monotonic.RRef

open Chacha_wip
open Poly.MAC

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module MAC = Crypto.Symmetric.Poly1305.MAC
module Chacha = Crypto.Symmetric.Chacha20

let u8  = UInt8.t
let u32 = UInt32.t
let u64 = UInt64.t

type domain = { nonce:u64; ctr:u32 } // could use lbytes 12 instead

let blockLen = 64ul
let block = b:bytes {Buffer.length b = v blockLen}

type lbytes (l:uint32) = b:bytes {Buffer.length b = v l}

// for now a bit too specific; 
// we should be parametric in i for the size of blocks, for conditional idealization,...

// the range of our PRF, after idealization and `reverse inlining`.

type range (i:id) (x:domain) = if x.ctr = 0ul then MAC.state i nonce else block 
type entry (i:id) = Entry: x:domain -> range i x -> entry i

// the PRF instance, including the key and memoization table
// TODO separate on rw, with multiple readers? 
type state (i:id) = 
  | State: rgn: HH.rid ->
           key:u32 -> 
           log:rref rgn (Seq.seq (entry i)) -> state i // should be maybe_mrref; for later. 

assume val random: nat -> ST (seq u8)
  (requires (fun m -> True))
  (ensures  (fun m0 _ m1 -> modifies Set.empty m0 m1))

assume val alloc_mref_seq: seq 'a -> ST (log_t 'a)
  (requires (fun m -> True))
  (ensures  (fun m0 _ m1 -> True ))

val gen: i:id -> ST (state i)
  (requires (fun h -> True))
  (ensures  (fun h0 s h1 -> True))

let gen i =
  let key = random 32 in
  let log = alloc_mref_seq Seq.createEmpty in
  State key log


// generates a PRF block and copies its len first bytes to output
let getBlock i t x len output = 
  Chacha.chacha20 output t.key x.iv x.ctr Chacha.constant len;


// We encapsulate the 3 usages of the PRF in specific functions.
// But we still use a single, ctr-dependent range in the table. 
//
// For xor-based encryption, 
// the ideal variant records both the plaintext and the ciphertext
// whereas the real PRF output is their xor.

// the first block (ctr=0) is used to generate a single-use MAC
val prf_mac: i:id -> t:state i -> x:domain -> ST MAC.state (i,x.nonce)
  (requires (fun h0 -> x.ctr = 0ul))
  (ensures 
    // we guarantee the stateful post of MAC.create when x is not in the table. 
    // in all cases, we return the state in the table
  )
  
// generates a fresh block for x and XORs it with plaintext
val prf_enxor: i:id -> t:state i -> x:domain -> l:uint32 -> plain:lbytes l -> cipher:lbytes l -> STL unit 
  (requires (fun h0 -> 
     x.ctr <> 0ul /\ live h0 plain /\ live h0 cipher /\
     is_None(lookupT h0 t.log x) 
     ))
  (ensures (fun h0 _ h1 -> 
     modifies_1 cipher h0 h1 /\
     match lookupT h0 t.log x with 
     | Some (p,c) -> sel_word h1 plain == p /\ sel_word h1 cipher = c
     | None -> False 
     ))

// reuse the same block for x and XORs it with ciphertext
val prf_dexor: i:id -> t:state i -> x:domain -> l:uint32 -> plain:lbytes l -> cipher:lbytes l -> STL unit 
  (requires (fun h0 -> 
     x.ctr <> 0ul /\ live h0 plain /\ live h0 cipher /\
     match lookupT h0 t.log x with 
     | None -> False
     | Some (p,c) -> sel_word h0 cipher == c
     ))
  (ensures (fun h0 _ h1 -> 
     modifies_1 plain h0 h1 /\
     match lookupT h0 t.log with 
     | Some (p,c) -> sel_word h1 plain == p
     | None -> False 
     ))

let prf_mac i t x = 
  if ideal then (
    match lookup t.log x with 
    | Some mac -> mac 
    | None     -> let mac = MAC.gen (i,nonce) t.rgn in 
                 append t.log (Entry x mac);
                 mac )
  else (
    let keyBytes = create 0uy keyLen in 
    getBlock t x keyLen keyBytes;
    coerce i t.rgn keyBytes )

let prf_enxor i t x l output input = 
  if ideal then (
    let c = random_seq l in  
    // store c into cipher 
    append t.log (Entry x (input,output)))
  else (
    getBlock t x l output;
    xor_bytes_inplace output input l ) 

let prf_dexor i t x l output input = 
  if ideal then ( 
    match lookup t.log x with 
    | Some (p,c) -> copy p to output )
  else (
    getBlock t x l output; 
    xor_bytes_inplace output input l )



