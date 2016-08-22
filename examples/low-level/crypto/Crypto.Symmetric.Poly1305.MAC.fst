module Crypto.Symmetric.Poly1305.MAC

open FStar.HyperHeap
open FStar.HyperStack
open FStar.HST
open FStar.Ghost
open FStar.UInt64
open FStar.Buffer
open FStar.HST.Monotonic.RRef

module HH = FStar.HyperHeap

// In AEAD_ChaCha20: id * nonce
assume new abstract type id

assume val authId: id -> Tot bool

type bytes = buffer (UInt8.t)

type lbytes (n:nat) = b:bytes{length b = n}

type tag = lbytes 16

noeq type msg =
  | Message: len:UInt32.t -> contents:bytes{length contents >= UInt32.v len} -> msg

type log = option (msg * tag)

assume val random: n:nat -> Tot (lbytes n)

let log_cmp (a:log) (b:log) =
  match a,b with
  | Some _, None -> False
  | Some x, Some y -> x == y
  | _ -> True

val log_cmp_reflexive: (a:log) -> Lemma
  (requires True)
  (ensures (log_cmp a a))
  [SMTPat (log_cmp a a)]
let log_cmp_reflexive a = ()

val log_cmp_transitive: a:log -> b:log -> c:log -> Lemma
  (requires True)
  (ensures (log_cmp a b /\ log_cmp b c ==> log_cmp a c))
let log_cmp_transitive a b c = ()

val log_cmp_monotonic: unit -> Lemma (monotonic log log_cmp)
let log_cmp_monotonic _ = ()

noeq type state (i:id) =
  | State:
      rid: rid ->
      key: lbytes 32 ->
      log: m_rref rid log log_cmp ->
      state i

val create: i:id -> r:rid -> ST (state i)
  (requires (fun m0 -> True))
  (ensures  (fun m0 st m1 ->
    modifies (Set.singleton r) m0 m1
    /\ m_contains st.log m1
    /\ is_None (m_sel m1 st.log)
  ))
let create i r =
  let key = random 32 in
  let log = m_alloc #log #log_cmp r None in
  State #i r key log

val coerce: i:id -> r:rid -> key:lbytes 32 -> ST (state i)
  (requires (fun m0 -> True))
  (ensures  (fun m0 st m1 ->
    modifies (Set.singleton r) m0 m1
    /\ m_contains st.log m1
    /\ is_None (m_sel m1 st.log)
    /\ ~(authId i)))
let coerce i r key =
  assume(~(authId i));
  let log = m_alloc #log #log_cmp r None in
  State #i r key log

type invoked (#i:id) (st:state i) (m:mem) : Type =
  is_Some (m_sel m st.log)

val mac: #i:id -> st:state i -> m:msg -> buf:bytes{lbytes 16} -> ST tag
  (requires (fun m0 -> is_None (m_sel m0 st.log)))
  (ensures  (fun m0 tag m1 ->
    modifies (Set.singleton (State.rid st)) m0 m1
    /\ modifies_rref st.rid !{HH.as_ref (as_rref st.log)} m0.h m1.h
    /\ witnessed (invoked #i st)
  ))
let mac #i st buf m =
  let tag =
    if authId i then
      random 16
    else
      let Message len contents = m in
      let () = Crypto.Symmetric.Poly1305.poly1305_mac buf contents len st.key in
      buf
    in
  m_recall st.log;
  m_write st.log (Some (m, tag));
  witness st.log (invoked #i st);
  tag

val bytes_cmp_: b:bytes -> b':bytes -> len:UInt32.t{UInt32.v len <= length b /\ UInt32.v len <= length b'} -> tmp:bool -> STL bool
  (requires (fun h -> live h b /\ live h b'))
  (ensures  (fun h0 z h1 -> live h0 b /\ live h0 b'
    /\ (b2t(z) <==> Seq.slice (as_seq h0 b) 0 (UInt32.v len) == Seq.slice (as_seq h0 b') 0 (UInt32.v len)) ))
let rec bytes_cmp_ b b' len tmp =
  let open FStar.UInt32 in
  if len =^ 0ul then tmp
  else 
    let i = len -^ 1ul in
    let bi = index b i in
    let bi' = index b' i in
    let open FStar.UInt8 in
    let tmp' = tmp && (bi =^ bi') in
    bytes_cmp_ b b' i tmp'

assume val bytes_cmp: b:bytes -> b':bytes -> len:UInt32.t{UInt32.v len <= length b /\ UInt32.v len <= length b'} -> STL bool
  (requires (fun h -> live h b /\ live h b'))
  (ensures  (fun h0 z h1 -> live h0 b /\ live h0 b'
    /\ (b2t(z) <==> Seq.slice (as_seq h0 b) 0 (UInt32.v len) == Seq.slice (as_seq h0 b') 0 (UInt32.v len)) ))

val verify: #i:id -> st:state i -> m:msg -> t:tag -> ST bool
  (requires (fun h0 -> True))
  (ensures (fun h0 valid h1 -> h0 == h1))
let verify #i st m t =
  if authId i then
    begin
    let log = m_read st.log in
    match log with
    | None -> false
    | Some (m', t') -> m' = m && t' = t
    end
  else
    let tag = Buffer.create 0uy 16ul in
    let () = Poly.Poly1305_wip.poly1305_mac tag m.contents m.len st.key in
    bytes_cmp tag t 16ul
