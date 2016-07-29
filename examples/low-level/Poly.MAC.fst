module Poly.MAC

open FStar
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HST
open FStar.Ghost
open FStar.UInt64
open FStar.Buffer
open FStar.STH

module MR = FStar.HST.Monotonic
module HH = FStar.HyperHeap

// In AEAD_ChaCha20: id * nonce
assume new abstract type id
assume val authId: id -> Tot bool

type bytes = buffer (UInt8.t)
type lbytes (n:nat) = b:bytes{length b = n}

type tag = lbytes 16
noeq type msg =
  | Message: len:(UInt32.t) -> contents:bytes{length contents >= UInt32.v len} -> msg
type log = option (msg * tag)

assume val random: n:nat -> Tot (lbytes n)

let log_cmp (a:log) (b:log) =
  match a,b with
  | Some _, None -> False
  | Some x, Some y -> x == y
  | _ -> True

val log_cmp_reflexive: (a:log) -> Lemma
  (requires (True))
  (ensures (log_cmp a a))
  [SMTPat (log_cmp a a)]
let log_cmp_reflexive a = ()

val log_cmp_transitive: a:log -> b:log -> c:log -> Lemma
  (requires (True))
  (ensures (log_cmp a b /\ log_cmp b c ==> log_cmp a c))
let log_cmp_transitive a b c = ()

val log_cmp_monotonic: unit -> Lemma (MR.monotonic log log_cmp)
let log_cmp_monotonic () = ()

noeq type state (i:id) =
  | State:
      rid : HH.rid ->
      key : lbytes 32 ->
      log : MR.m_rref rid log log_cmp ->
      state i

let create (i:id) (r:rid)
  : STH (state i)
  (requires (fun h0 -> True))
  (ensures (fun h0 st h1 ->
    let log = MR.as_rref st.log in
    modifies (Set.singleton r) h0 h1
    /\ contains_ref log h1
    /\ is_None (HH.sel h1 log)
  ))
  =
  let key = random 32 in
  let log = MR.m_alloc #log #log_cmp r None in
  State #i r key log

let coerce (i:id) (r:rid) (key:lbytes 32)
  : STH (state i)
  (requires (fun h0 -> True))
  (ensures (fun h0 st h1 ->
    let log = MR.as_rref st.log in
    modifies (Set.singleton r) h0 h1
    /\ contains_ref log h1
    /\ is_None (HH.sel h1 log)
    /\ ~(authId i)))
  =
  assume(~(authId i));
  let log = MR.m_alloc #log #log_cmp r None in
  State #i r key log

type invoked (#i:id) (st:state i) (h:HH.t) =
  b2t (is_Some (HH.sel h (MR.as_rref st.log)))

let mac (#i:id) (st:state i) (m:msg)
  : STH tag 
  (requires (fun h0 -> is_None (HH.sel h0 (MR.as_rref st.log))))
  (ensures (fun h0 tag h1 ->
    modifies (Set.singleton (State.rid st)) h0 h1
    /\ modifies_rref st.rid !{HH.as_ref (MR.as_rref st.log)} h0 h1
    /\ MR.witnessed (invoked #i st)
  ))
  =
  let tag =
    if authId i then
      random 16
    else
      let tag = create 0uy 16ul in
      let Message len contents = msg in
      let () = Poly.Poly1305_wip.poly1305_mac tag contents len st.key in
      tag
    in
  MR.m_write st.log (Some (m, tag));
  MR.witness st.log (invoked #i st);
  tag

let verify (#i:id) (st:state i) (m:msg) (t:tag)
  : STH bool
  (requires (fun h0 -> True))
  (ensures (fun h0 valid h1 -> h0 == h1))
  =
  false

