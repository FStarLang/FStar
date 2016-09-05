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

let u64 = UInt64.t

let block = lbytes 64

noeq type entry (i:id) =
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
