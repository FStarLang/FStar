module Poly.MAC

open FStar.HyperStack
open FStar.HST
open FStar.Ghost
open FStar.UInt64
open FStar.Buffer

module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap

// In AEAD_ChaCha20: id * nonce
assume new abstract type id
assume val authId: id -> bool

type bytes = buffer (UInt8.t)
type lbytes (n:nat) = b:bytes{length b = n}

type tag = lbytes 16
type msg =
  | Message: len:(UInt32.t) -> contents:bytes{length contents >= Uint32.v len} -> msg
type log = option (msg * tag)

assume val random: n:nat -> lbytes n

let log_cmp (a:log) (b:log) =
  match a,b with
  | None, None
  | None, Some _
  | Some (a,b), Some (a',b') -> (a=a' && b=b')
  | _ -> False

val opt_bool_monotonic: unit -> Lemma (MR.monotonic log log_cmp)
let opt_bool_monotonic () = ()

type state (i:id) =
  | State:
      #i  : id ->
      rid : HH.rid ->
      key : lbytes 32 ->
      log : MR.m_rref rid log log_cmp ->
      state i

let create (i:id) (r:rid) : HST (state i) =
  let key = random 32 in
  let log = MR.m_alloc #log #log_cmp r None in
  State #i r key log

let coerce (i:id) (r:rid) (key:lbytes 32) : HST (state i) =
  assume(~(authId i));
  let log = MR.m_alloc #log #log_cmp r None in
  State #i r key log




