module Crypto.Symmetric.Poly1305.MAC

(* Provides idealization layer for multiplicative MACs; 
   could use the same code for both POLY1305 and GCM.
   
*)

open FStar.HyperHeap
open FStar.HyperStack
open FStar.HST
open FStar.Ghost
open FStar.UInt64
open FStar.Buffer

// not working?
//open FStar.HST.Monotonic.RRef

open Crypto.Symmetric.Poly1305.Spec
open Crypto.Symmetric.Poly1305 
// avoid?

let norm = Crypto.Symmetric.Poly1305.Bigint.norm 

// also used in miTLS ('model' may be better than 'idea'); could be loaded from another module.
// this flag enables conditional idealization by keeping additional data,
// - this should not affect the code behavior
// - this may cause the code not to compile to Kremlin/C.
let ideal = true 


module HH = FStar.HyperHeap

// to be rewired. 
// In AEAD_ChaCha20: id * nonce
assume new abstract type id
assume val authId: id -> Tot bool

type bytes = buffer (UInt8.t)

type lbytes (n:nat) = b:bytes{length b = n}

type tag = wordB_16

noeq type msg =
  | Message: len:UInt32.t -> contents:bytes{length contents >= UInt32.v len} -> msg

(*
// TODO: extend the model with dynamic compromises.
type log_1 = 
  | Init 
  | MACed: msg -> tag -> log 
  | Corrupt

type log_2 = // only when ideal
//  | MACing: seq elem -> log 
  | Init
  | MACed: seq elem -> tag -> log
  | Corrupt
*)

assume val random: n:nat -> Tot (lbytes n)

type log = option(Seq.seq msg * word_16)

(* TODO: restore monotonicity 
let log_cmp (a:log) (b:log) =
  match a,b with
  | Some (l,t) , Some (l',t') -> Seq.eq l l' && t = t'
  | None, _                   -> true
  | _                         -> false

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

type slog rid = (if ideal then m_rref rid log log_cmp else unit)
*) 
type slog rid = (if ideal then rref rid log else unit)

// the sequence of hashed elements is conditional, but not ghost
// this will require changing e.g. the type of poly1305_add
let ilog : Type0 = if ideal then Seq.seq msg else unit

assume val log_0: ilog
//let log_0 : ilog = if ideal then let l:ilog = Seq.createEmpty #elem in l else ()

noeq type state (i:id) =
  | State:
      rid: rid ->
      r  : elemB ->
      s  : wordB_16 ->
      log: slog rid ->
      state i

val alloc: i:id -> r:rid{is_eternal_region r} -> key:bytes {length key >= 32} -> st0: log -> ST (state i)
  (requires (fun m0 -> live m0 key))
  (ensures  (fun m0 st m1 ->
    modifies (Set.singleton r) m0 m1
    // todo: /\ r and s are fresh, as specified in poly1305_init 
    // /\ m_contains st.log m1
    // /\ is_None (m_sel m1 st.log)
  ))

#set-options "--lax" 
let alloc i rid key st0 = 
  let r = FStar.Buffer.rcreate rid 0UL 5ul in
  let s = FStar.Buffer.rcreate rid 0uy 16ul in  
  let _ = poly1305_init r s key in 
  //let log = m_alloc #log #log_cmp rid st0 in
  let log = ralloc #log rid st0 in
  State #i rid r s log

(*
val create: i:id -> r:rid -> ST (state i)
  (requires (fun m0 -> True))
  (ensures  (fun m0 st m1 ->
    modifies (Set.singleton r) m0 m1
    /\ m_contains st.log m1
    /\ is_None (m_sel m1 st.log)
  ))
*)
let create i rid =
  let key = random 32 in
  alloc i rid key None

(*
val coerce: i:id -> r:rid -> key:lbytes 32 -> ST (state i)
  (requires (fun m0 -> True))
  (ensures  (fun m0 st m1 ->
    modifies (Set.singleton r) m0 m1
    /\ m_contains st.log m1
    /\ is_None (m_sel m1 st.log)
    /\ ~(authId i)))
*)    
let coerce i rid key =
  assume(~(authId i));
  alloc i rid key None

(*
type invoked (#i:id) (st:state i) (m:mem) : Type =
  ideal /\ is_Some (sel m (State.log st))

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
*)

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



(* in the concrete code... 

let recomputed = ... in
verify i st received recomputed

*)

// we will need authId i ==> ideal 


// a partial multiplicative-mac computation
// (considered secret, declassified only via mac and declassify)
//
// We need to isolate the state of partial MAC computations.
// the key state is now clamped
// we use state-passing in the spec (to be reviewed)
// not sure what to record for separation.

abstract type accB (i:id) = elemB

let accB_inv (#i:id) (st:state i) (l: ilog) a h = 
  let r = sel_elem h st.r in 
  let a = sel_elem h a in 
  (ideal ==> a = poly l r)

// not framed, as we allocate private state on the caller stack
val start: #i:id -> st:state i -> STL (accB i)
  (requires (fun h0 -> True))
  (ensures (fun h0 a h1 -> 
    // allocated, and... 
    accB_inv st (Seq.createEmpty #elem) a h1
  ))

val update: #i:id -> st:state i -> l:ilog -> computed:accB i -> v:elemB -> ST unit
  (requires (fun h0 -> // "liveness" /\ 
    accB_inv st log computed h0))
  (ensures (fun h0 () h1 -> 
    // "liveness" /\ "modifies computed" /\
    accB_inv st (FStar.SeqProperties.snoc l (sel_elem h1 v)) computed h1))
let update #i st vs a v = 
  add_and_multiply a v st.r 


val mac: #i:id -> st:state i -> l:ilog -> computed:accB i -> tag: wordB -> ST unit
  (requires (fun h0 -> ideal ==> 
    sel_elem h0 computed = poly l (sel_elem h0 st.r)  /\
    HyperStack.sel h0 st.log = None #log))
  (ensures (fun h0 _ h1 -> 
    // modifies h0 h1 "the tag buffer and st.log" /\ 
    let s: word_16 = sel_word h0 st.s in 
    let mac = mac_1305 l (sel_elem h0 st.r) s in
    mac = little_endian (sel_word h1 tag) /\
    (authId i ==> HyperStack.sel h1 st.log = Some (l,mac))))

let mac #i st vs acc tag = 
  poly1305_finish tag acc st.s;
  if ideal then st.log := (Some (vs,read_word tag))

val verify: #i:id -> st:state i -> l:ilog -> computed:accB i -> tag:wordB_16 -> 
  ST bool
  (requires (fun h0 -> ideal ==> 
    sel_elem h0 computed = poly l (sel_elem h0 st.r)))
  (ensures (fun h0 b h1 -> 
    h0 == h1 /\ (
    let mac = mac_1305 l (sel_elem h0 st.r) (sel_word h0 st.s) in
    let verified = mac = little_endian (sel_word h1 tag) in
    let correct = HyperStack.sel h0 st.log = Some (l,mac) in 
    b = verified && (not (authId i) || correct))))

let verify #i st l acc received =
  let tag = Buffer.create 0uy 16ul in  
  poly1305_finish tag acc st.s;
  let verified = bytes_cmp tag received 16ul in 
  if ideal && authId i then 
    let st = !st.log in 
    let correct = st = Some(l,read_word tag) in
    verified && correct
  else  
    verified

(*
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
*)


// this code is not involved in the idealization;
// it could go elsewhere, e.g. in AEAD

// adapted from Poly1305.poly1305_update
val add:
  #i:id ->
  st: state i ->
  l0: ilog -> 
  a: accB i ->
  w:wordB_16 -> STL ilog
  (requires (fun h -> live h w /\ live h a /\ norm h a /\ norm h st.r
    /\ (ideal ==> sel_elem h a = poly l0 (sel_elem h st.r))))
  (ensures (fun h0 l1 h1 -> 
    modifies_1 a h0 h1 /\ norm h1 a /\ 
    (ideal ==> l1 = SeqProperties.snoc l0 (encode_16 (sel_word h0 w)) /\
             sel_elem h1 a = poly l1 (sel_elem h0 st.r))))

let add #i st l0 a w = 
  push_frame();
  (* TODO: re-use the elem buffer rather that create a fresh one, maybe in the accumulator *)
  let e = Buffer.create 0UL Crypto.Symmetric.Poly1305.Parameters.nlength in
  toField_plus_2_128 e w;
  update st l0 a e;
  let h = HST.get() in
  let msg = esel_word h w in
  let l1 = Ghost.elift2 (fun log msg -> update_log log (encode_16 msg)) l0 msg in
  pop_frame();
  l1

let sel_bytes (h:mem) (b:bytes{live h b}) : GTot (Seq.seq UInt8.t)
  = as_seq h b

(*
assume val encode_pad: Seq.seq UInt8.t -> Tot (Seq.seq elem)

val loop:
  #i:id ->
  st: state i ->
  l0: ilog -> 
  a: accB i ->
  txt:bytes -> STL ilog
  (requires (fun h -> live h txt /\ live h a /\ norm h a /\ norm h st.r
    /\ (ideal ==> sel_elem h a = poly l0 (sel_elem h st.r))))
  (ensures (fun h0 l1 h1 -> 
    modifies_1 a h0 h1 /\ 
    live h1 txt /\ live h1 a /\ norm h1 a /\ 
    (ideal ==> l1 = Seq.append l0 (encode_pad (sel_bytes h0 txt)) /\
             sel_elem h1 a = poly l1 (sel_elem h0 st.r))))

let rec loop #i st l0 a txt ctr =
  if ctr = 0 then l0 else 
  begin
    let w = sub txt 0ul 16ul in
    let l1 = add st l0 a w in 
    let txt1 = offset txt 16ul in
    loop st l1 a txt1 (ctr - 1)
  end
*)
