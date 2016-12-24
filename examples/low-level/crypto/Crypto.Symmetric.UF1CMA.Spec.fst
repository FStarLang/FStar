(**
   This file states our probabilistic security assumption on
   polynomial MACs, and provides an idealized implementation,
   while being abstract on the underlying field.
*)
module Crypto.Symmetric.UF1CMA.Spec

open Crypto.Symmetric.MAC.Spec
open Crypto.Symmetric.Bytes
open Crypto.Indexing
open Flag

open FStar.HyperHeap
open FStar.HyperStack

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module RR = FStar.Monotonic.RRef


(** Authenticated payload: a sequence of words *)
type text = Seq.seq word_16
type tag  = tag

(** One-time MAC log, None or Some (m, MAC(m)) *)
type log = option (text * tag) 

let log_cmp (a:log) (b:log) =
  match a,b with
  | Some (l,t) , Some (l',t') -> l == l' /\ t == t' // avoid inversion
  | None, _                   -> True
  | _                         -> False

val log_cmp_monotonic: unit -> Lemma (RR.monotonic log log_cmp)
let log_cmp_monotonic _ = ()

let erid = r:HH.rid{HS.is_eternal_region r}

let ideal_log (r:erid) = RR.m_rref r log log_cmp

let log_ref (r:erid) = if mac_log then ideal_log r else unit

let ilog (#r:erid) (l:log_ref r{mac_log}) : Tot (ideal_log r) = l

type alg = macAlg

let alg_of_id = macAlg_of_id

noeq type state (i:id) =
  | State:
    #region: erid ->
    r: elem (alg_of_id i) ->
    s: word_16 ->
    log: log_ref region ->
    state i


(** Length of the single-use part of the key *)
let keylen (i:id) = 
  match aeadAlg_of_id i with
  | AES_128_GCM       -> 16ul
  | AES_256_GCM       -> 16ul
  | CHACHA20_POLY1305 -> 32ul

(** Length of optional static auth key (when using AES) *)
let skeylen (i:id) =  // can't refine with {skeyed i} here
  match aeadAlg_of_id i with
  | AES_128_GCM       -> 16ul
  | AES_256_GCM       -> 16ul
  | _                 ->  0ul // dummy; never allocated.

(** Does the algorithm use a static key? *)
let skeyed (i:id) = 
  match aeadAlg_of_id i with
  | AES_128_GCM       -> true
  | AES_256_GCM       -> true
  | CHACHA20_POLY1305 -> false

type key (i:id) = b:bytes{Seq.length b = UInt32.v (keylen i)}
type skey (i:id) = b:bytes{Seq.length b = UInt32.v (skeylen i)}
type akey (i:id) = o:option (skey i){is_Some o <==> skeyed i}

val get_skey: #i:id{skeyed i} -> akey i -> Tot (skey i)
let get_skey #i (Some k) = k

let genPost (i:id) (region:erid) m0 (st:state i) m1 =
   st.region == region /\
   (mac_log ==>
      ~(RR.m_contains (ilog st.log) m0) /\
      RR.m_contains (ilog st.log) m1 /\
      RR.m_sel m1 (ilog st.log) == None)

val alloc: region:erid -> i:id
  -> ak:akey i
  -> k: key i
  -> ST (state i)
  (requires (fun m0 -> true))
  (ensures  (fun m0 st m1 -> genPost i region m0 st m1 /\ HS.modifies_one region m0 m1))
let alloc region i ak k =
  let (rb,sb):(lbytes 16 * lbytes 16) =
    if skeyed i then
      get_skey #i ak, k 
    else
       Seq.slice k 0 16, Seq.slice k 16 32
  in
  let r = encode rb in
  let s:word_16 = sb in
  if mac_log then
    begin
    log_cmp_monotonic ();
    let log = RR.m_alloc #log #log_cmp region None in
    State #i #region r s log
    end
  else
    State #i #region r s ()

val gen: region:erid -> i:id -> ak:akey i -> ST (state i)
  (requires (fun m0 -> true))
  (ensures (fun m0 st m1 -> genPost i region m0 st m1 /\ HS.modifies_one region m0 m1))
let gen region i ak =
  let len = keylen i in
  let k = random_bytes len in
  alloc region i ak k


assume val authId: id -> Tot bool

val coerce: region:erid -> i:id{~(authId i)}
  -> ak:akey i
  -> k:key i
  -> ST (state i)
  (requires (fun m0 -> true))
  (ensures (fun m0 st m1 -> genPost i region m0 st m1 /\ HS.modifies_one region m0 m1))
let coerce region i ak k =
  alloc region i ak k

let irtext = if mac_log then HS.reference text else unit

noeq abstract type accBuffer (i:id) =
  | Acc: a:elem (alg_of_id i) ->
         l:irtext ->
         accBuffer i

let alog (#i:id) (acc:accBuffer i{mac_log}) : HS.reference text =
  acc.l

let acc_inv (#i:id) (st:state i) (acc:accBuffer i) h =
  (mac_log ==> (
    let log = HS.sel h (alog acc) in
    let a = acc.a in
    let r = st.r in
    HS.contains h (alog acc) /\
    a == poly_eval #(alg_of_id i) (encode_text log) r))


val start: #i:id -> st:state i -> StackInline (accBuffer i)
  (requires (fun h -> true))
  (ensures  (fun h0 a h1 ->
    acc_inv st a h1 /\ 
    h0 = h1))

let start #i st =
  let t:text = Seq.createEmpty #word_16 in
  let log:irtext = if mac_log then HS.ref t else () in
  let a = zero #(alg_of_id i) in
  Acc #i a log
