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
module Block = Crypto.Symmetric.Chacha20

let u64 = UInt64.t

let blockLen = 64ul
let block = b:bytes {Buffer.length b = v blockLen}


// for now a bit too specific; 
// we should be parametric in i for the size of blocks, for conditional idealization,...

// the range of our PRF, after idealization and `reverse inlining`.

type domain = { nonce:u64; ctr:u32 } // could use lbytes 12 instead

type range (i:id) (x:domain) = if x.ctr = 0ul then MAC.state i nonce else block 
type entry (i:id) = Entry: x:domain -> range i x -> entry i

// the PRF instance, including the key and memoization table
// TODO separate on rw, with multiple readers? 
type state (i:id) = | State: 
  rgn:i:id -> 
  key:u32 -> 
  log:rref rgn (Seq.seq (entry i)) -> state i // should be maybe_mrref; for later. 

val prf_xor_1: key -> nonce -> ctr:u32 { ctr <> 0ul } -> msg:block -> Tot block
val prf_xor: t -> nonce -> ctr:u32 { ctr <> 0ul } -> msg:block -> Tot block

let prf_xor t nonce ctr msg = memoize t (fun () -> prf_xor_1 t.key nonce ctr msg)

// for clarity, we use separate functions for each use of the PRF
// But we still use a single, ctr-dependent range in the table. 

let prf_mac i t (x:domain {x.ctr = 0ul}) = 
  if ideal then 
    begin 
      match lookup t.log with 
      | Some mac -> mac 
      | None     -> let mac = MAC.gen (i,nonce) t.rgn in 
                   write_at_end t.log (Entry iv ctr mac);
                   mac 
    end
  else
    let block = create 0ul blockLen in 
    Block.chacha20 block t.key iv ctr Block.constant blockLen;
    coerce i t.rgn (sub block 0ul MAC.keyLen)
    
  memoize t.log (fun () -> 


let prf_xor t iv ctr maybe_block = 
  if ideal then 
    memoize (fun nonce ctr maybe_block -> 
      if x.ctr = 0ul 
      then 
      else random blockLen)
  else
    let block = create 0ul blockLen in 
    Block.chacha20 block t.key iv ctr Block.constant blockLen; //TODO truncate last block
    if ctr = 0ul then 
      coerce i region (sub block 0ul MAC.keyLen)
    else
      xor_bytes_inplace cipher plain len


 | MAC:  nonce:u64           -> block:block -> entry i
 | Mask: nonce:u64 -> ctr:u32 -> block:block -> entry i

let log_ref (r:rid) (i:id) = log_t r (entry i)

noeq type state (i:id) =
  | State: rid: HH.rid
         -> key: lbytes 32
         -> log: log_ref i
	 -> state i

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


