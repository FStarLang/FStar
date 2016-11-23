module Crypto.Symmetric.UF1CMA

(* this file states our probabilistic security assumption on
   polynomial MACs, and provides an idealized implementation,
   while being abstract on the underlying field. *)

open FStar.HyperHeap
open FStar.HyperStack
open FStar.Ghost
open FStar.UInt64
open FStar.Buffer
open FStar.Monotonic.RRef

open Crypto.Symmetric.Poly1305.Spec
open Crypto.Symmetric.Poly1305 // avoid?
open Crypto.Symmetric.Bytes
open Crypto.Indexing
open Flag

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MAC = Crypto.Symmetric.MAC

// library stuff

type alg = macAlg
let alg_of_id = macAlg_of_id

 
// TOWARDS AGILITY 

// length of the single-use part of the key
let keylen (i:id) = 
  match aeadAlg_of_id i with
  | AES_128_GCM       -> 16ul
  | AES_256_GCM       -> 16ul
  | CHACHA20_POLY1305 -> 32ul

// OPTIONAL STATIC AUTHENTICATION KEY (when using AES)
let skeylen (i:id) =  // can't refine with {skeyed i} here
  match aeadAlg_of_id i with
  | AES_128_GCM       -> 16ul
  | AES_256_GCM       -> 16ul
  | _                 ->  0ul // dummy; never allocated.

let skeyed (i:id) = 
  match aeadAlg_of_id i with
  | AES_128_GCM       -> true
  | AES_256_GCM       -> true
  | CHACHA20_POLY1305 -> false

type skey (rgn:rid) (i:id) = b:lbuffer (UInt32.v (skeylen i)){ Buffer.frameOf b = rgn}

// conditionally-allocated, abstract key (accessed only in this module)
//16-10-16 can't make it abstract?
let akey (rgn:rid) (i:id) = 
  o:option (skey rgn i) {is_Some #(skey rgn i) o <==> skeyed i}
  // 16-10-28 
  // using a sum type for kremlin; was:
  // if skeyed i then skey rgn i else unit

val get_skey: #r:rid -> #i:id{skeyed i} -> akey r i -> Tot (skey r i)
let get_skey #rgn #i (Some k) = k

val akey_gen: r:rid -> i:id -> STL(akey r i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> Buffer.modifies_0 h0 h1))

val akey_coerce: r:rid -> i:id -> kb: lbuffer(UInt32.v (skeylen i)) -> STL(akey r i)
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> Buffer.modifies_0 h0 h1))

val akey_gen: r:rid -> i:id -> ST (akey r i)
  (requires (fun _ -> True))
  (ensures  (fun h0 k h1 ->
    if skeyed i then
      HS.modifies (Set.singleton r) h0 h1 /\
      HS.modifies_ref r TSet.empty h0 h1 /\
      (~(live h0 (get_skey #r #i k)) /\ live h1 (get_skey #r #i k))
    else h0 == h1))
let akey_gen r i =
  if skeyed i 
  then
    let k:skey r i = Buffer.rcreate r 0uy (skeylen i) in
    Some k
  else None

val akey_coerce: r:rid -> i:id -> kb:lbuffer (UInt32.v (skeylen i)) -> ST (akey r i)
  (requires (fun h -> live h kb))
  (ensures  (fun h0 k h1 ->
    if skeyed i then
      HS.modifies (Set.singleton r) h0 h1 /\
      HS.modifies_ref r TSet.empty h0 h1 /\
      (~(live h0 (get_skey #r #i k)) /\ live h1 (get_skey #r #i k))
    else h0 == h1))
let akey_coerce r i kb =
  if skeyed i 
  then
    let sk:skey r i = Buffer.rcreate r 0uy (skeylen i) in
    let h1 = ST.get () in
    Buffer.blit kb 0ul sk 0ul (skeylen i);
    let h2 = ST.get () in
    lemma_reveal_modifies_1 sk h1 h2;
    Some sk
  else None

// ONE-TIME INSTANCES
type id = MAC.id

// also used in miTLS ('model' may be better than 'ideal'); could be loaded from another module.
// this flag enables conditional idealization by keeping additional data,
// - this should not affect the code behavior
// - this may cause the code not to compile to Kremlin/C.
(* inline_for_extraction *) 
unfold let authId (i:id) =
  let i = fst i in
  safeHS i && mac1 i

// we will need authId i ==> ideal?

// the index is the base index (controlling agility and idealization)
// plus the value of the unique IV for this MAC
// TODO make it a dependent pair to support agile IV types

// authenticated payload: a sequence of words
type text = Seq.seq (lbytes 16)
type log = option (text * tag) 

let log_cmp (a:log) (b:log) =
  match a,b with
  | Some (l,t) , Some (l',t') -> l == l' /\ t == t'
  | None, _                   -> True
  | _                         -> False

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

let ideal_log (r:rid) = m_rref r log log_cmp

let log_ref (r:rid) = if mac_log then ideal_log r else unit

let ilog (#r:rid) (l:log_ref r{mac_log}) : Tot (ideal_log r) = l

noeq type state (i:id) =
  | State:
      #region: rid ->
      r: MAC.elemB i{Buffer.frameOf (MAC.as_buffer r) = region} -> 
      s: wordB_16 {frameOf s = region /\ disjoint (MAC.as_buffer r) s} ->
      log: log_ref region ->
      state i

let live_ak #r (#i:id) m (ak:akey r (fst i)) = 
  skeyed (fst i) ==> live m (get_skey #r #(fst i) ak)

let genPost0 (i:id) (region:rid{is_eternal_region region}) m0 (st: state i) m1 =
    ~(contains m0 (MAC.as_buffer st.r)) /\
    ~(contains m0 st.s) /\
    st.region == region /\
    MAC.norm m1 st.r /\
    Buffer.live m1 st.s /\
    (mac_log ==> 
        ~ (m_contains (ilog st.log) m0) /\ 
	   m_contains (ilog st.log) m1 /\ 
	   m_sel m1 (ilog st.log) == None)

let genPost (i:id) (region:rid{is_eternal_region region}) m0 (st:state i) m1 =
  genPost0 i region m0 st m1 /\
  modifies (Set.singleton region) m0 m1 /\
  modifies_rref region TSet.empty m0.h m1.h

val alloc: region:rid{is_eternal_region region} -> i:id
  -> ak:akey region (fst i)
  -> k:lbuffer (UInt32.v (keylen (fst i)))
  -> ST (state i)
  (requires (fun m0 -> live m0 k /\ live_ak m0 ak))
  (ensures  (fun m0 st m1 -> genPost i region m0 st m1))
 //   (skeyed (fst i) ==> modifies_1 (get_skey #region #(fst i) st.r) m0 m1)

#reset-options "--z3timeout 30 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

let alloc region i sk k =
  let h0 = ST.get() in
  let r = MAC.rcreate region i in
  assert (frameOf (MAC.as_buffer r) == region);
  let s = FStar.Buffer.rcreate region 0uy 16ul in
  cut (disjoint (MAC.as_buffer r) k /\ disjoint s k);
  let h1 = ST.get() in
  let rb, sb =
    if skeyed (fst i) then
      get_skey #region #(fst i) sk, k
    else
      sub k 0ul 16ul, sub k 16ul 16ul
  in
  MAC.encode_r r rb;
  let h2 = ST.get() in
  lemma_reveal_modifies_2 (MAC.as_buffer r) rb h1 h2;
  Buffer.blit sb 0ul s 0ul 16ul; 
  let h3 = ST.get() in
  lemma_reveal_modifies_1 s h2 h3;
  assume (MAC.norm h3 r);
  assume False;
  if mac_log then
    let log = m_alloc #log #log_cmp region None in
    let h4 = ST.get() in
    assume (MAC.norm h4 r);
    State #i #region r s log
  else
    State #i #region r s ()


// for now, we require an eternal region to get monotonicity
val gen: region:rid{is_eternal_region region} -> i:id -> ak:akey region (fst i) -> ST (state i)
  (requires (fun m0 -> live_ak m0 ak))
  (ensures (genPost i region))

let gen region i ak =
  let len = keylen (fst i) in
  let k = FStar.Buffer.rcreate region 0uy len in
  let h0 = ST.get() in
  random (UInt32.v len) k;
  let h1 = ST.get () in
  lemma_reveal_modifies_1 k h0 h1;
  alloc region i ak k
//
//let gen rgn i st0 = 
//  let r_buff = 
//    if static_r i then st0 
//    else encode_r (random 16ul) in
//  let s = random 16ul in
//  alloc rgn i r_buff s

val coerce: 
  r:rid -> i:id{~(authId i)} -> 
  ak: akey r (fst i)  -> 
  k:lbuffer (UInt32.v (keylen (fst i))) -> ST (state i)
  (requires (fun m0 -> live m0 k /\ live_ak m0 ak))
  (ensures  (genPost i r))

let coerce region i k0 k = alloc region i k0 k


// HASH ACCUMULATORS (SEVERAL FOR EACH INSTANCE) 

// a partial multiplicative-mac computation
// (considered secret, declassified only via mac and declassify)

// We need to isolate the state of partial MAC computations.
// the key state is now clamped
// we use state-passing in the spec (to be reviewed)
// not sure what to record for separation.

// should be abstract, but then we need to duplicate more elemB code

let irtext = if mac_log then FStar.HyperStack.reference text else unit

let mk_irtext (r:HS.reference text{mac_log}) : irtext = r

// 16-10-15 still missing region, needed for modifies clauses below!
noeq abstract type accBuffer (i:id) = 
  | Acc: a:MAC.elemB i -> l:irtext -> accBuffer i

let alog (#i:id) (acc:accBuffer i {mac_log}): HS.reference text = acc.l

let acc_inv (#i:id) (st:state i) (acc:accBuffer i) h =
  MAC.live h st.r /\ MAC.live h acc.a /\ //not sure why I need those, implied by norm
  MAC.norm h st.r /\ MAC.norm h acc.a /\ 
  disjoint (MAC.as_buffer st.r) (MAC.as_buffer acc.a) /\
  (mac_log ==> (
    let log = FStar.HyperStack.sel h (alog acc) in
    let a = MAC.sel_elem h acc.a in
    let r = MAC.sel_elem h st.r in
    a == MAC.poly log r))
      
// not framed, as we allocate private state on the caller stack
val start: #i:id -> st:state i -> StackInline (accBuffer i)
  (requires (fun h -> MAC.norm h st.r))
  (ensures  (fun h0 a h1 -> 
    ~ (h0 `Buffer.contains` (MAC.as_buffer a.a)) /\
    acc_inv st a h1 /\ 
    modifies_0 h0 h1))
let start #i st =
  let a = MAC.start #i in
  let l = if mac_log then mk_irtext (salloc Seq.createEmpty) else () in
  assume False;
  Acc a l


// update [was add]; could add finalize (for POLY1305, last block < 16).
val update:
  #i:id ->
  st: state i ->
  a: accBuffer i ->
  w: lbuffer 16 -> STL unit
  (requires (fun h -> acc_inv st a h /\ Buffer.live h w))
  (ensures (fun h0 l1 h1 ->
    // TODO. modifying both a buffer and its ref seq bytes (if present)
    // acc_modifies a h0 h1 /\  
    Buffer.live h1 w /\ 
    acc_inv st a h1 /\ 
    (mac_log ==> (
      let v = Buffer.as_seq h1 w in
      HS.sel h1 (alog a) == SeqProperties.cons v (HS.sel h0 (alog a))))))

let update #i st acc w =
  //16-10-17 if mac_log then acc.l <- SeqProperties.cons w !aac.l;
  assume false; //16-10-17 
  MAC.update st.r acc.a w


#reset-options "--z3timeout 100 --lax"
(*
val mk_itext: s:Seq.seq (lbytes 16){Flag.mac_log} -> itext
let mk_itext s = s
*)

val mac: 
  #i:id -> 
  st:state i -> 
  acc:accBuffer i -> 
  tag:lbuffer 16 -> ST unit
  (requires (fun h0 ->
    live h0 tag /\ live h0 st.s /\
    disjoint_2 (MAC.as_buffer acc.a) st.s tag /\ 
    disjoint_2 (MAC.as_buffer st.r) st.s tag /\
    disjoint st.s tag /\ 
    acc_inv st acc h0 /\
    (mac_log ==> m_contains (ilog st.log) h0) /\
    (mac_log /\ authId i ==> m_sel h0 (ilog st.log) == None)))
  (ensures (fun h0 _ h1 ->
    live h0 st.s /\ 
    live h0 (MAC.as_buffer st.r) /\ 
    live h1 tag /\
    acc_inv st acc h0 /\ (
    if mac_log then 
      mods [Ref (as_hsref (ilog st.log)); Ref (Buffer.content tag)] h0 h1 /\
      Buffer.modifies_buf_1 (Buffer.frameOf tag) tag h0 h1 /\
      m_contains (ilog st.log) h1 /\ (
      let log = FStar.HyperStack.sel h1 (alog acc) in
      let a = MAC.sel_elem h1 acc.a in
      let r = MAC.sel_elem h1 st.r in
      let s = Buffer.as_seq h1 st.s in
      let t = MAC.mac log r s in
      sel_word h1 tag === t /\
      m_sel h1 (ilog st.log) == Some(log,t)
      )
    else
      Buffer.modifies_1 tag h0 h1 )))

let mac #i st acc tag =
  let h0 = ST.get () in
  assert(MAC.live h0 acc.a);
  assert(MAC.norm h0 acc.a);
  MAC.finish st.s acc.a tag;
  let h1 = ST.get () in
  if mac_log then
    begin
      //assume (mac_1305 l (sel_elem h0 st.r) (sel_word h0 st.s) == little_endian (sel_word h1 tag));
      let t = load_bytes 16ul tag in
      let l = !(alog acc) in
      m_recall #st.region #log #log_cmp (ilog st.log);
      assume (m_sel h1 (ilog st.log) == m_sel h0 (ilog st.log));
      m_write #st.region #log #log_cmp (ilog st.log) (Some (l, t))
    end
  else
    admit ()


val verify: 
  #i:id -> 
  st:state i -> 
  acc:accBuffer i -> 
  tag:lbuffer 16 -> Stack bool
  (requires (fun h0 -> 
    live h0 tag /\ live h0 st.s /\
    disjoint_2 (MAC.as_buffer acc.a) st.s tag /\ 
    disjoint_2 (MAC.as_buffer st.r) st.s tag /\
    acc_inv st acc h0 /\
    (mac_log ==> m_contains (ilog st.log) h0) /\
    (mac_log /\ authId i ==> is_Some (m_sel h0 (ilog st.log)))))
        
  (ensures (fun h0 b h1 ->
    Buffer.modifies_0 h0 h1 /\
    live h0 st.s /\ 
    live h0 (MAC.as_buffer st.r) /\ 
    live h1 tag /\
    acc_inv st acc h0 /\ (
    if mac_log then 
      let log = FStar.HyperStack.sel h1 (alog acc) in
      let r = MAC.sel_elem h1 st.r in
      let s = Buffer.as_seq h1 st.s in
      let m = MAC.mac log r s in
      let verified = Seq.eq m (sel_word h1 tag) in
      b = 
      ( if authId i then 
          let correct = 
          ( match m_sel h0 (ilog st.log) with 
            | Some(l',m') -> m = m' && Seq.eq log l'
            | None -> false ) in
          verified && correct
        else verified)
    else true)))

let verify #i st acc received =
  assume false; //16-10-30 
  push_frame();
  let tag = Buffer.create 0uy 16ul in
  MAC.finish st.s acc.a tag;
  let verified = Buffer.eqb tag received 16ul in
  let b =
  if mac_log && authId i then
    let st = !st.log in
    let t = load_bytes 16ul tag in
    let l = !(alog acc) in
    let correct = 
      match st with 
      | Some(l',t') -> t' = t && Seq.eq l l' 
      | None -> false in
    verified && correct
  else
    verified in
  pop_frame();
  b
