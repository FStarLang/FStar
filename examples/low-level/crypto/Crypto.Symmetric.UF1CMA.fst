(**
   This file states our probabilistic security assumption on
   polynomial MACs, and provides an idealized implementation,
   while being abstract on the underlying field.
*)
module Crypto.Symmetric.UF1CMA

open FStar.HyperHeap
open FStar.HyperStack
open FStar.Ghost
open FStar.UInt64
open FStar.Buffer

open Crypto.Symmetric.Poly1305.Spec
open Crypto.Symmetric.Poly1305 // avoid?
open Crypto.Symmetric.Bytes
open Crypto.Indexing
open Flag

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module RR = FStar.Monotonic.RRef
module MAC = Crypto.Symmetric.MAC


// should go elsewhere
let erid = r:rid{is_eternal_region r}

type alg = macAlg

let alg_of_id = macAlg_of_id

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

type skey (rgn:rid) (i:id) =
  b:lbuffer (UInt32.v (skeylen i)){Buffer.frameOf b == rgn}

//16-10-16 can't make it abstract?
(** Conditionally-allocated abstract key (accessed only in this module) *)
let akey (rgn:rid) (i:id) = 
  o:option (skey rgn i) {Some? o <==> skeyed i}
  // using a sum type for KreMLin. Was: if skeyed i then skey rgn i else unit

val get_skey: #r:rid -> #i:id{skeyed i} -> akey r i -> Tot (skey r i)
let get_skey #rgn #i (Some k) = k


val akey_gen: r:erid -> i:id -> ST (akey r i)
  (requires (fun _ -> True))
  (ensures  (fun h0 k h1 ->
    if skeyed i then
      HS.modifies (Set.singleton r) h0 h1 /\
      HS.modifies_ref r TSet.empty h0 h1 /\
      ~(live h0 (get_skey #r #i k)) /\
      live h1 (get_skey #r #i k)
    else h0 == h1))
let akey_gen r i =
  if skeyed i then
    let k:skey r i = Buffer.rcreate r 0uy (skeylen i) in
    Some k
  else None


val akey_coerce: r:erid -> i:id -> kb:lbuffer (UInt32.v (skeylen i)) -> ST (akey r i)
  (requires (fun h -> live h kb))
  (ensures  (fun h0 k h1 ->
    if skeyed i then
      HS.modifies (Set.singleton r) h0 h1 /\
      HS.modifies_ref r TSet.empty h0 h1 /\
      ~(live h0 (get_skey #r #i k)) /\
      live h1 (get_skey #r #i k)
    else h0 == h1))
let akey_coerce r i kb =
  if skeyed i then
    let sk:skey r i = Buffer.rcreate r 0uy (skeylen i) in
    let h1 = ST.get () in
    Buffer.blit kb 0ul sk 0ul (skeylen i);
    let h2 = ST.get () in
    lemma_reveal_modifies_1 sk h1 h2;
    Some sk
  else None


(** One-time MAC instance *)
type id = MAC.id

(**
 * Also used in miTLS ('model' may be better than 'ideal');
 * could be loaded from another module.
 * This flag enables conditional idealization by keeping additional data:
 * - this should not affect the code behavior
 * - this may cause the code not to compile to KreMLin/C
 *)
unfold let authId (i:id) = // inline_for_extraction?
  let i = fst i in
  safeHS i && mac1 i

// Do we need authId i ==> ideal?

// the index is the base index (controlling agility and idealization)
// plus the value of the unique IV for this MAC
// TODO make it a dependent pair to support agile IV types

(** Authenticated payload: a sequence of words *)
type text = Seq.seq (lbytes 16)

(** One-time MAC log, None or Some (m, MAC(m)) *)
type log = option (text * tag) 

let log_cmp (a:log) (b:log) =
  match a,b with
  | Some (l,t) , Some (l',t') -> l == l' /\ t == t' // avoid inversion
  | None, _                   -> True
  | _                         -> False

val log_cmp_monotonic: unit -> Lemma (RR.monotonic log log_cmp)
let log_cmp_monotonic _ = ()

let ideal_log (r:erid) = RR.m_rref r log log_cmp

let log_ref (r:erid) = if mac_log then ideal_log r else unit

let ilog (#r:erid) (l:log_ref r{mac_log}) : Tot (ideal_log r) = l

noeq type state (i:id) =
  | State:
    #region: erid ->
    r: MAC.elemB i{Buffer.frameOf (MAC.as_buffer r) == region} ->
    s: wordB_16{frameOf s == region /\ disjoint (MAC.as_buffer r) s} ->
    log: log_ref region ->
    state i

let live_ak #r (#i:id) m (ak:akey r (fst i)) = 
  skeyed (fst i) ==> live m (get_skey #r #(fst i) ak)


let genPost (i:id) (region:erid) m0 (st:state i) m1 =
   ~(contains m0 (MAC.as_buffer st.r)) /\
   ~(contains m0 st.s) /\
   st.region == region /\
   MAC.norm m1 st.r /\
   Buffer.live m1 st.s /\
   (mac_log ==>
      ~(RR.m_contains (ilog st.log) m0) /\
      RR.m_contains (ilog st.log) m1 /\
      RR.m_sel m1 (ilog st.log) == None)

#set-options "--z3rlimit 60 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val alloc: region:erid -> i:id
  -> ak:akey region (fst i)
  // Could live in a different region, but this simplifies the spec
  -> k:lbuffer (UInt32.v (keylen (fst i))){frameOf k == region}
  -> ST (state i)
  (requires (fun m0 -> live m0 k /\ live_ak m0 ak))
  (ensures  (fun m0 st m1 -> genPost i region m0 st m1 /\ modifies_one region m0 m1))
#reset-options "--z3rlimit 100"
let alloc region i ak k =
  let r = MAC.rcreate region i in
  let s = FStar.Buffer.rcreate region 0uy 16ul in
  let h1 = ST.get () in
  let rb, sb =
    if skeyed (fst i) then
      get_skey #region #(fst i) ak, k
    else
      sub k 0ul 16ul, sub k 16ul 16ul
  in
  MAC.encode_r r rb;
  let h2 = ST.get () in
  lemma_reveal_modifies_2 (MAC.as_buffer r) rb h1 h2;
  Buffer.blit sb 0ul s 0ul 16ul;
  let h3 = ST.get () in
  lemma_reveal_modifies_1 s h2 h3;
  if mac_log then
    begin
    log_cmp_monotonic ();
    let log = RR.m_alloc #log #log_cmp region None in
    State #i #region r s log
    end
  else
    State #i #region r s ()


val gen: region:erid -> i:id -> ak:akey region (fst i) -> ST (state i)
  (requires (fun m0 -> live_ak m0 ak))
  (ensures (fun m0 st m1 -> genPost i region m0 st m1 /\ modifies_one region m0 m1))
let gen region i ak =
  let len = keylen (fst i) in
  let k = FStar.Buffer.rcreate region 0uy len in
  let h0 = ST.get() in
  random (UInt32.v len) k;
  let h1 = ST.get () in
  lemma_reveal_modifies_1 k h0 h1;
  alloc region i ak k


val coerce: region:erid -> i:id{~(authId i)}
  -> ak:akey region (fst i)
  -> k:lbuffer (UInt32.v (keylen (fst i))){frameOf k == region}
  -> ST (state i)
  (requires (fun m0 -> live m0 k /\ live_ak m0 ak))
  (ensures (fun m0 st m1 -> genPost i region m0 st m1 /\ modifies_one region m0 m1))
let coerce region i ak k =
  alloc region i ak k


(** Hash accumulators (several per instance)

  A partial multiplicative MAC computation
  (considered secret, declassified only via mac and declassify)

  We need to isolate the state of partial MAC computations.
  The key state is now clamped
  We use state-passing in the spec (to be reviewed)
  Not sure what to record for separation.
*)

(** Should be abstract, but causes code duplication *)
let irtext (r:rid) = if mac_log then (x:HS.reference text{x.id == r}) else unit

noeq abstract type accBuffer (i:id) =
  | Acc: a:MAC.elemB i ->
         l:irtext (Buffer.frameOf (MAC.as_buffer a)) ->
         accBuffer i

let alog (#i:id) (acc:accBuffer i{mac_log}) : HS.reference text =
  acc.l

val abuf: #i:id -> acc:accBuffer i -> GTot (MAC.elemB i)
let abuf #i acc = acc.a

let acc_inv (#i:id) (st:state i) (acc:accBuffer i) h =
  MAC.norm h st.r /\ MAC.norm h acc.a /\
  disjoint (MAC.as_buffer st.r) (MAC.as_buffer acc.a) /\
  (mac_log ==> (
    let log = HS.sel h (alog acc) in
    let a = MAC.sel_elem h acc.a in
    let r = MAC.sel_elem h st.r in
    HS.contains h (alog acc) /\
    disjoint_ref_1 (MAC.as_buffer acc.a) (HS.as_aref (alog acc)) /\
    disjoint_ref_1 (MAC.as_buffer st.r)  (HS.as_aref (alog acc)) /\
    a == MAC.poly log r))

#set-options "--z3rlimit 100"

// not framed, as we allocate private state on the caller stack
val start: #i:id -> st:state i -> StackInline (accBuffer i)
  (requires (fun h -> MAC.norm h st.r))
  (ensures  (fun h0 a h1 ->
    Buffer.frameOf (MAC.as_buffer a.a) == h1.tip /\
    ~(h0 `Buffer.contains` (MAC.as_buffer a.a)) /\
    acc_inv st a h1 /\
    modifies_0 h0 h1))

let start #i st =
  let h0 = ST.get () in
  let a = MAC.start #i in
  let h1 = ST.get () in
  lemma_reveal_modifies_0 h0 h1;
  if mac_log then
    let log = salloc #text Seq.createEmpty in
    let h2 = ST.get () in
    // Needed to prove disjointness of st.r and log
    assert (HS.sel h2 (Buffer.content (MAC.as_buffer st.r)) =!= Seq.createEmpty);
    lemma_intro_modifies_0 h0 h2;
    MAC.frame_sel_elem h1 h2 a;
    MAC.poly_empty #i (HS.sel h2 log) (MAC.sel_elem h2 st.r);
    Acc #i a log
  else
    Acc #i a ()


let modifies_buf_and_ref (#a:Type) (#b:Type) (buf:Buffer.buffer a) (ref:reference b) h h' : GTot Type0 =
  (forall rid. Set.mem rid (Map.domain h.h) ==>
    HH.modifies_rref rid !{Buffer.as_ref buf, HS.as_ref ref} h.h h'.h
    /\ (forall (#a:Type) (b:Buffer.buffer a). 
      (frameOf b == rid /\ live h b /\ disjoint b buf
      /\ disjoint_ref_1 b (HS.as_aref ref)) ==> equal h b h' b))

// update [was add]; could add finalize (for POLY1305 when last block < 16).
val update: #i:id -> st:state i -> acc:accBuffer i -> w:lbuffer 16 ->
  Stack unit
  (requires (fun h ->
    acc_inv st acc h /\
    Buffer.live h w /\
    Buffer.disjoint (MAC.as_buffer acc.a) w /\
    Buffer.disjoint (MAC.as_buffer st.r) w /\
    (mac_log ==> Buffer.disjoint_ref_1 w (HS.as_aref (alog acc))) ))
  (ensures  (fun h0 _ h1 ->
     acc_inv st acc h1 /\
     Buffer.live h0 w /\
     (if mac_log then
       HS.sel h1 (alog acc) ==
       SeqProperties.cons (Buffer.as_seq h0 w) (HS.sel h0 (alog acc)) /\
       (let buf = MAC.as_buffer acc.a in
        let rid = frameOf buf in
        //Alternative 1:
        //HS.modifies (Set.singleton rid) h0 h1 /\
        //HS.modifies_ref rid (TSet.singleton (FStar.Heap.Ref (HS.as_ref (alog acc)))) h0 h1 /\
        //Buffer.modifies_buf_1 rid buf h0 h1)
        // Alternative 2:
        //modifies_bufs_and_refs 
        //  (Buffer.only buf) (TSet.singleton (HS.as_aref (alog acc))) h0 h1)
        // Alternative 3 (works):
        modifies_buf_and_ref buf (alog acc) h0 h1) 
     else
       Buffer.modifies_1 (MAC.as_buffer acc.a) h0 h1) ))

let update #i st acc w =
  let h0 = ST.get () in
  if mac_log then
    begin
    let v = read_word 16ul w in
    let vs = !(alog acc) in
    acc.l := SeqProperties.cons v vs;
    let h1 = ST.get () in
    MAC.frame_sel_elem h0 h1 st.r;
    MAC.frame_sel_elem h0 h1 acc.a;
    MAC.poly_cons #i v vs (MAC.sel_elem h0 st.r)
    end;
  let h1 = ST.get () in
  MAC.update st.r acc.a w;
  let h2 = ST.get () in
  lemma_reveal_modifies_1 (MAC.as_buffer acc.a) h1 h2;
  MAC.frame_sel_elem h1 h2 st.r


#set-options "--lax"

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
    (mac_log ==> RR.m_contains (ilog st.log) h0) /\
    (mac_log /\ authId i ==> RR.m_sel h0 (ilog st.log) == None)))
  (ensures (fun h0 _ h1 ->
    live h0 st.s /\ 
    live h0 (MAC.as_buffer st.r) /\ 
    live h1 tag /\
    acc_inv st acc h0 /\ (
    if mac_log then 
      mods [Ref (RR.as_hsref (ilog st.log)); Ref (Buffer.content tag)] h0 h1 /\
      Buffer.modifies_buf_1 (Buffer.frameOf tag) tag h0 h1 /\
      RR.m_contains (ilog st.log) h1 /\ (
      let log = FStar.HyperStack.sel h1 (alog acc) in
      let a = MAC.sel_elem h1 acc.a in
      let r = MAC.sel_elem h1 st.r in
      let s = Buffer.as_seq h1 st.s in
      let t = MAC.mac log r s in
      sel_word h1 tag === t /\
      RR.m_sel h1 (ilog st.log) == Some(log,t))
    else
      Buffer.modifies_1 tag h0 h1)))

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
      RR.m_recall #st.region #log #log_cmp (ilog st.log);
      assume (RR.m_sel h1 (ilog st.log) == RR.m_sel h0 (ilog st.log));
      RR.m_write #st.region #log #log_cmp (ilog st.log) (Some (l, t))
    end


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
    (mac_log ==> RR.m_contains (ilog st.log) h0) /\
    (mac_log /\ authId i ==> Some? (RR.m_sel h0 (ilog st.log)))))
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
      (if authId i then
          let correct = 
          (match RR.m_sel h0 (ilog st.log) with
           | Some(l',m') -> m = m' && Seq.eq log l'
           | None -> false) in
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
