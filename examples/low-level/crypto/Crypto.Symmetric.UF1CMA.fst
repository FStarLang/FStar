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
open Flag 

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MAC = Crypto.Symmetric.MAC

// library stuff

type alg = Flag.mac_alg
let alg_of_id = Flag.cipher_of_id


 
// TOWARDS AGILITY 

// length of the single-use part of the key
let keylen (i:id) = 
  match i.cipher with 
  | AES_256_GCM       -> 16ul
  | CHACHA20_POLY1305 -> 32ul




// OPTIONAL STATIC AUTHENTICATION KEY (when using AES)

let skeyed (i:id) = 
  match i.cipher with 
  | AES_256_GCM       -> true
  | CHACHA20_POLY1305 -> false

let skeylen (i:id {skeyed i}) = 
  match i.cipher with 
  | AES_256_GCM       -> 16ul

type skey (rgn:rid) (i:id{skeyed i}) = b:lbuffer (UInt32.v (skeylen i)){ Buffer.frameOf b = rgn}

// conditionally-allocated, abstract key (accessed only in this module)
//16-10-16 can't make it abstract?
let akey (rgn:rid) (i:id) = if skeyed i then skey rgn i else unit

private val get_skey: #r:rid -> #i:id{skeyed i} -> akey r i -> Tot(skey r i)
let get_skey #rgn #i k = k

private val mk_akey: #r:rid -> #i:id{skeyed i} -> skey r i -> Tot(akey r i)
let mk_akey #rgn #i k = k

//16-10-16 without the #r #i below, getting
//16-10-16 Error: Unexpected error... Failure("Bound term variable not found (after unmangling): ww___#215762")
let akey_gen (r:rid) (i:id) = 
  if skeyed i then mk_akey #r #i (Buffer.rcreate r 0uy (skeylen i))
  else ()

(* should be called at most once per i *)


// ONE-TIME INSTANCES 

type id = Flag.id * UInt128.t

// also used in miTLS ('model' may be better than 'ideal'); could be loaded from another module.
// this flag enables conditional idealization by keeping additional data,
// - this should not affect the code behavior
// - this may cause the code not to compile to Kremlin/C.
(* inline_for_extraction *) 
unfold let authId (i: id) =
  let i = fst i in
  safeHS i && mac1 i

// we will need authId i ==> ideal?

// the index is the base index (controlling agility and idealization)
// plus the value of the unique IV for this MAC
// TODO make it a dependent pair to support agile IV types


// the sequence of hashed elements is conditional, but not ghost
type text = Seq.seq (lbytes 16)
let itext: Type0 = if Flag.mac_log then text else unit

type log = option (itext * tag) // option (Seq.seq elem * word16)

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
      r: MAC.elemB (fst i){Buffer.frameOf r = region} -> 
      s: wordB_16 {frameOf s = region} ->
      log: log_ref region ->
      state i

let genPost0 (i:id) (region:rid{is_eternal_region region}) m0 (st: state i) m1 =
    ~(contains m0 st.r) /\
    ~(contains m0 st.s) /\
    st.region == region /\
    MAC.live m1 st.r /\
    (mac_log ==> 
        ~ (m_contains (ilog st.log) m0) /\ 
	   m_contains (ilog st.log) m1 /\ 
	   m_sel m1 (ilog st.log) == None)

let genPost (i:id) (region:rid{is_eternal_region region}) m0 (st: state i) m1 =
    genPost0 i region m0 st m1 /\
    modifies (Set.singleton region) m0 m1 /\ 
    modifies_rref region TSet.empty m0.h m1.h  

val alloc: i:id
  -> region:rid{is_eternal_region region}
  -> key:lbuffer 32
  -> ST (state i)
  (requires (fun m0 -> live m0 key))
  (ensures  (genPost i region))
 
#reset-options "--z3timeout 100"
let alloc i region key =
  let r = MAC.rcreate region (fst i) in
  let s = FStar.Buffer.rcreate region 0uy 16ul in
  assume false;//16-10-17 TODO
  cut (disjoint r key /\ disjoint s key);
  let h0 = ST.get() in
  MAC.encode_r (fst i) r (sub key 0ul 16ul);
  Buffer.blit key 16ul s 0ul 16ul; 
  // note that we never call poly1305_init r s key;
  // consider restoring it for stateful verification
  let h1 = ST.get() in
  lemma_reveal_modifies_2 r s h0 h1;
  if mac_log then
    let log = m_alloc #log #log_cmp region None in
    //16-10-16 missing frame
    let h2 = ST.get() in
    assume (MAC.live h1 r ==> MAC.live h2 r);
    State #i #region r s log
  else
    State #i #region r s ()
//
//let alloc rgn i r_buff s = 
//  let r = encode_r r_buff in 
//  let log = ref None in 
//  State i r s log

// for now, we require an eternal region to get monotonicity
val gen: i:id -> region:rid{is_eternal_region region} -> ST (state i)
  (requires (fun m0 -> True))
  (ensures (genPost i region))

let gen i region =
  let key = FStar.Buffer.rcreate region 0uy 32ul in
  let h0 = ST.get() in
  random 32 key;
  let h1 = ST.get () in
  lemma_reveal_modifies_1 key h0 h1;
  alloc i region key
//
//let gen rgn i st0 = 
//  let r_buff = 
//    if static_r i then st0 
//    else encode_r (random 16ul) in
//  let s = random 16ul in
//  alloc rgn i r_buff s

val coerce: i:id{~(authId i)} -> r:rid -> key:lbuffer 32 -> ST (state i)
  (requires (fun m0 -> live m0 key))
  (ensures  (genPost i r))

let coerce i region key =
  alloc i region key



// HASH ACCUMULATORS (SEVERAL FOR EACH INSTANCE) 

// a partial multiplicative-mac computation
// (considered secret, declassified only via mac and declassify)

// We need to isolate the state of partial MAC computations.
// the key state is now clamped
// we use state-passing in the spec (to be reviewed)
// not sure what to record for separation.

// should be abstract, but then we need to duplicate more elemB code

let irtext i = if mac_log then FStar.HyperStack.reference (Seq.seq (MAC.elem i)) else unit

let mk_irtext (#i:id{mac_log}) (r:HS.reference (Seq.seq (MAC.elem (fst i)))) : irtext (fst i) = r

// 16-10-15 still missing region, needed for modifies clauses below!
noeq type accBuffer (i:id) = 
  | Acc:  a:MAC.elemB (fst i) -> l:irtext (fst i) -> accBuffer i

let alog (#i:id) (acc:accBuffer i {mac_log}): HS.reference (Seq.seq (MAC.elem (fst i))) = acc.l


let acc_inv (#i:id) (st:state i) (acc:accBuffer i) h =
  MAC.live h st.r /\ MAC.live h acc.a /\ disjoint st.r acc.a /\
  (mac_log ==> (
    let log = FStar.HyperStack.sel h (alog acc) in
    let a = MAC.sel_elem h acc.a in
    let r = MAC.sel_elem h st.r in
    a == MAC.poly #(fst i) log r))
    
// not framed, as we allocate private state on the caller stack
val start: #i:id -> st:state i -> StackInline (accBuffer i)
  (requires (fun h -> MAC.live h st.r))
  (ensures  (fun h0 a h1 -> acc_inv st a h1 /\ modifies_0 h0 h1))
let start #i st =
  let a = MAC.start (fst i) in
  let l = if mac_log then mk_irtext #i (salloc (Seq.createEmpty #(MAC.elem (fst i)))) else () in
  assume false;//16-10-17 TODO
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
      let e = MAC.encode h1 (fst i) (Buffer.as_seq h1 w) in
      HS.sel h1 (alog a) == SeqProperties.cons e (HS.sel h0 (alog a))))))

let update #i st acc w =
  //16-10-17 if mac_log then acc.l <- SeqProperties.cons w !aac.l;
  assume false; //16-10-17 
  MAC.update st.r acc.a w


(* 16-10-17 to be continued... 

val mac: 
  #i:id -> 
  st:state i -> 
  acc:accBuffer i -> 
  tag:lbuffer 16 -> ST unit
  (requires (fun h0 ->
    live h0 tag /\ live h0 st.s /\
    disjoint acc st.s /\ disjoint tag acc /\ disjoint tag st.r /\ disjoint tag st.s /\
    acc_inv st acc h0 /\
    (mac_log ==> m_sel h0 (ilog st.log) == None)))
  (ensures (fun h0 _ h1 ->
    live h0 st.s /\ live h0 st.r /\ live h1 tag /\
    // modifies h0 h1 "the tag buffer and st.log" /\
    (mac_log ==> (
      let log = FStar.HyperStack.sel h1 (alog acc) in
      let a = MAC.sel_elem h1 acc.a in
      let r = MAC.sel_elem h1 st.r in
      let s = Buffer.as_seq h1 st.s in
      let m = MAC.mac i log r s in
      a == MAC.poly #(fst i) log r /\
      m = little_endian (sel_word h1 tag) /\
      m_sel h1 (ilog st.log) == Some (log, m)))))

val verify: #i:id -> st:state i -> computed:accB i -> tag:tagB -> Stack bool
  (requires (fun h0 -> acc_inv st a h0))
  (ensures (fun h0 b h1 ->
    Buffer.modifies_0 h0 h1 /\
    (let m = MAC.mac i (coeffs acc) (sel_elem h0 st.r) (sel_word h0 st.s) in
     let verified = m = little_endian (sel_word h1 tag) in
     b = 
       (if mac_log && authId i then 
       let correct = 
         (match HyperStack.sel h0 st.log with 
         | Some(l',m') -> m = m' && MAC.equal (coeffs acc) l'
         | None -> false ) in
       verified && correct
       else verified))))

let mac #i st acc tag =
  let h0 = ST.get () in
  MAC.finish st acc tag;
  let h1 = ST.get () in
  if mac_log then
    begin
      //assume (mac_1305 l (sel_elem h0 st.r) (sel_word h0 st.s) == little_endian (sel_word h1 tag));
      let t = read_word tag in
      m_recall #st.region #log #log_cmp (ilog st.log);
      assume (m_sel h1 (ilog st.log) == m_sel h0 (ilog st.log));
      m_write #st.region #log #log_cmp (ilog st.log) (Some (l, t))
    end
  else
    admit ()

let verify #i st acc received =
  push_frame();
  let tag = Buffer.create 0uy 16ul in
  MAC.finish st acc tag;
  let verified = Buffer.eqb tag received 16ul in

  let b = 
  if mac_log && authId i then
    let st = !st.log in
    let correct = 
      match st with 
      | Some(l',m') -> m' = read_word tag && MAC.equal (coeffs acc) l' 
      | None -> false in
    verified && correct
  else
    verified in

  pop_frame();
  b

*)
