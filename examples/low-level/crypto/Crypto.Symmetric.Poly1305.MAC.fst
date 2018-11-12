module Crypto.Symmetric.Poly1305.MAC

(* Provides idealization layer for multiplicative MACs;
   could use the same code for both POLY1305 and GCM.
*)

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
// library stuff

let norm h b = Crypto.Symmetric.Poly1305.Bigint.norm h b
 
// TOWARDS AGILITY 

// length of the single-use part of the key
let keylen (i:id) = 
  match aeadAlg_of_id i with 
  | AES_256_GCM       -> 16ul
  | CHACHA20_POLY1305 -> 32ul

// OPTIONAL STATIC AUTHENTICATION KEY (when using AES)

let skeyed (i:id) = 
  match aeadAlg_of_id i with 
  | AES_256_GCM       -> true
  | CHACHA20_POLY1305 -> false

let skeylen (i:id {skeyed i}) = 
  match aeadAlg_of_id i with 
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
//16-10-16 Error: Unexpected error... Failure("Bound term variable not found (after unmangling): uu___#215762")
let akey_gen (r:rid) (i:id) = 
  if skeyed i then mk_akey #r #i (Buffer.rcreate r 0uy (skeylen i))
  else ()

type id = id * UInt128.t

// also used in miTLS ('model' may be better than 'ideal'); could be loaded from another module.
// this flag enables conditional idealization by keeping additional data,
// - this should not affect the code behavior
// - this may cause the code not to compile to Kremlin/C.
(* inline_for_extraction *) unfold let authId (i: id) =
  let i = fst i in
  safeHS i && mac1 i

// we will need authId i ==> ideal?

// the index is the base index (controlling agility and idealization)
// plus the value of the unique IV for this MAC
// TODO make it a dependent pair to support agile IV types

assume val someId: i:Crypto.Indexing.id{~(safeHS i)} // dummy value for unit testing

(*
type id = nat
let authId i = false
let someId = 0
*)

type tagB = wordB_16
type wordB_16 = wordB_16

(*
// TODO: extend the model with dynamic compromises.
type log_1 =
  | Init
  | MACed: msg -> Spec.log > log
  | Corrupt

type log_2 = // only when ideal
//  | MACing: text -> log
  | Init
  | MACed: text -> Spec.log -> log
  | Corrupt
*)

// the sequence of hashed elements is conditional, but not ghost
// this will require changing e.g. the type of poly1305_add
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

let text_0: itext = if mac_log then Seq.empty #elem else ()

// we have "norm h r" only as a state invariant
noeq type state (i:id) =
  | State:
      #region: rid ->
      r: elemB {frameOf r = region} -> 
      s: wordB_16 {frameOf s = region} ->
      log: log_ref region ->
      state i

let genPost (i:id) (region:rid{is_eternal_region region}) m0 (st: state i) m1 =
    ~(contains m0 st.r) /\
    ~(contains m0 st.s) /\
    st.region == region /\
    norm m1 st.r /\
    Buffer.live m1 st.s /\
    (mac_log ==> 
        ~ (m_contains (ilog st.log) m0) /\ 
	   m_contains (ilog st.log) m1 /\ 
	   m_sel m1 (ilog st.log) == None)

let genPost (i:id) (region:rid{is_eternal_region region}) m0 (st: state i) m1 =
    genPost i region m0 st m1 /\
    modifies (Set.singleton region) m0 m1 /\ 
    modifies_rref region TSet.empty m0.h m1.h 

val alloc: i:id
  -> region:rid{is_eternal_region region}
  -> key:lbuffer 32
  -> ST (state i)
  (requires (fun m0 -> live m0 key))
  (ensures  (genPost i region))

#reset-options "--z3rlimit 100"
let alloc i region key =
  let r = FStar.Buffer.rcreate region 0UL 5ul in
  let s = FStar.Buffer.rcreate region 0uy 16ul in
  cut (disjoint r key /\ disjoint s key);
  let h0 = ST.get() in
  poly1305_init r s key;
  let h1 = ST.get() in
  lemma_reveal_modifies_2 r s h0 h1;
  if mac_log then
    let log = m_alloc #log #log_cmp region None in
    State #i #region r s log
  else
    State #i #region r s ()

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

val coerce: i:id{~(authId i)} -> r:rid -> key:lbuffer 32 -> ST (state i)
  (requires (fun m0 -> live m0 key))
  (ensures  (genPost i r))

let coerce i region key =
  alloc i region key

// a partial multiplicative-mac computation
// (considered secret, declassified only via mac and declassify)

// We need to isolate the state of partial MAC computations.
// the key state is now clamped
// we use state-passing in the spec (to be reviewed)
// not sure what to record for separation.

// should be abstract, but then we need to duplicate more elemB code
type accB (i:id) = elemB

// 16-10-15 TODO mac_log ==> keep stateful itext (to avoid state-passing)
// 16-10-15 still missing region
let irtext = if Flag.mac_log then FStar.HyperStack.ref text else unit 
noeq type accBuffer (i:id) = | Acc:  l:irtext -> a:elemB -> accBuffer i
let alog (#i:id) (acc:accBuffer i {mac_log}): FStar.HyperStack.ref text = acc.l
let acc_inv'(#i:id) (st:state i) (acc:accBuffer i) h =
  live h st.r /\ live h acc.a /\ disjoint st.r acc.a /\
  norm h st.r /\ norm h acc.a /\
  (mac_log ==> (
    let log = FStar.HyperStack.sel h (alog acc) in
    sel_elem h acc.a == poly log (sel_elem h st.r)))


let acc_inv (#i:id) (st:state i) (l:itext) (a:accB i) h =
  live h st.r /\ live h a /\ disjoint st.r a /\
  norm h st.r /\ norm h a /\
  (let r = sel_elem h st.r in
   let a = sel_elem h a in
   mac_log ==> a == poly l r)

// not framed, as we allocate private state on the caller stack
val start: #i:id -> st:state i -> StackInline (accB i)
  (requires (fun h -> live h st.r /\ norm h st.r))
  (ensures  (fun h0 a h1 -> 
	       ~ (h0 `Buffer.contains` a) /\
	       acc_inv st text_0 a h1 /\ 
	       modifies_0 h0 h1))
let start #i st =
  let h0 = ST.get () in
  let a = Buffer.create 0UL 5ul in
  let h1 = ST.get () in
  //lemma_reveal_modifies_0 h0 h1;
  assert (equal h0 st.r h1 st.r);
  poly1305_start a;
  let h2 = ST.get () in
  //lemma_reveal_modifies_1 a h1 h2;
  assert (equal h1 st.r h2 st.r);
  Bigint.norm_eq_lemma h0 h2 st.r st.r;
  a

val update: #i:id -> st:state i -> l:itext -> a:accB i -> v:elemB -> Stack itext
  (requires (fun h0 ->
    disjoint st.r v /\
    disjoint a v /\
    norm h0 v /\
    acc_inv st l a h0))
  (ensures (fun h0 l1 h1 ->
    modifies_1 a h0 h1 /\
    acc_inv st l1 a h1))

assume val sel_elemT: b:elemB -> ST elem
  (requires (fun h0 -> live h0 b))
  (ensures  (fun h0 r h1 -> h0 == h1 /\ live h0 b /\ r == sel_elem h0 b))

val seq_head_snoc: #a:Type -> xs:Seq.seq a -> x:a ->
  Lemma (requires True)
        (ensures Seq.length (Seq.snoc xs x) > 0 /\
                 seq_head (Seq.snoc xs x) == xs)
let seq_head_snoc #a xs x =
  Seq.lemma_len_append xs (Seq.create 1 x);
  Seq.lemma_eq_intro (seq_head (Seq.snoc xs x)) xs

#reset-options "--z3rlimit 100 --print_fuels --initial_fuel 1 --initial_ifuel 1"

let update #i st l a v =
  let h0 = ST.get () in
  add_and_multiply a v st.r;
  let h1 = ST.get () in
  //lemma_reveal_modifies_1 a h0 h1;
  Bigint.eval_eq_lemma h0 h1 st.r st.r Parameters.norm_length;
  Bigint.eval_eq_lemma h0 h1 v v Parameters.norm_length;
  (* Bigint.norm_eq_lemma h0 h1 st.r st.r; *)
  (* Bigint.norm_eq_lemma h0 h1 v v; *)
  //assert (sel_elem h1 a == (sel_elem h0 a +@ sel_elem h0 v) *@ sel_elem h0 st.r);
  //assert (live h1 st.r /\ live h1 a /\ disjoint st.r a);
  //assert (norm h1 st.r /\ norm h1 a);
  //assert (sel_elem h0 st.r == sel_elem h1 st.r);
  //assert (sel_elem h0 v == sel_elem h1 v);
  if mac_log then
    let v = sel_elemT v in
    let vs = Seq.snoc l v in
    Seq.lemma_index_app2 l (Seq.create 1 v) (Seq.length vs - 1);
    seq_head_snoc l v;
    //assert (Seq.index vs (Seq.length vs - 1) == v');
    //assert (seq_head vs == l);
    //assert (sel_elem h1 a == (poly (seq_head vs) (sel_elem h0 st.r) +@ Seq.index vs (Seq.length vs - 1)) *@ (sel_elem h1 st.r));
    vs

#reset-options


(*
type invoked (#i:id) (st:state i) (m:mem) : Type =
  mac_log /\ Some? (sel m (State.log st))

val mac: #i:id -> st:state i -> m:msg -> buf:buffer{lbytes 16} -> ST tag
  (requires (fun m0 -> None? (m_sel m0 st.log)))
  (ensures  (fun m0 tag m1 ->
    modifies (Set.singleton (State.rid st)) m0 m1
    /\ modifies_rref st.rid !{HH.as_ref (as_rref st.log)} m0.h m1.h
    /\ witnessed (invoked #i st)))
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
(*
let acc_inv (#i:id) (st:state i) (l:itext) (a:accB i) h =
  live h st.r /\ live h a /\ disjoint st.r a /\
  norm h st.r /\ norm h a /\
  (let r = sel_elem h st.r in
   let a = sel_elem h a in
   mac_log ==> a == poly l r)
*)

#reset-options "--z3rlimit 20 --initial_fuel 1 --initial_ifuel 1 --max_fuel 1 --max_ifuel 1"

let trigger_rid (r:rid) = True

unfold let mods_2 (rs:some_refs) h0 h1 =
    modifies (normalize_term (regions_of_some_refs rs)) h0 h1
  /\ (forall (r:rid).{:pattern (trigger_rid r)} 
	        trigger_rid r /\
                modifies_ref r (normalize_term (refs_in_region r rs)) h0 h1)


val mac: #i:id -> st:state i -> l:itext -> acc:accB i -> tag:tagB -> ST unit
  (requires (fun h0 ->
    live h0 tag /\ live h0 st.s /\
    disjoint acc st.s /\ disjoint tag acc /\ disjoint tag st.r /\ disjoint tag st.s /\
    acc_inv st l acc h0 /\
    (mac_log ==> m_contains (ilog st.log) h0) /\
    (mac_log /\ safeId (fst i) ==> m_sel h0 (ilog st.log) == None)))
  (ensures (fun h0 _ h1 ->
    live h0 st.s /\ 
    live h0 st.r /\ 
    live h1 tag /\ (
    if mac_log then
      mods_2 [Ref (as_hsref (ilog st.log)); Ref (Buffer.content tag)] h0 h1 /\
      Buffer.modifies_buf_1 (Buffer.frameOf tag) tag h0 h1 /\
      HS.modifies_ref st.region !{HS.as_ref (as_hsref (ilog st.log))} h0 h1 /\
      m_contains (ilog st.log) h1 /\ (
      let mac = mac_1305 l (sel_elem h0 st.r) (sel_word h0 st.s) in
      mac == sel_word h1 tag /\
      m_sel h1 (ilog st.log) == Some (l, sel_word h1 tag))
    else Buffer.modifies_1 tag h0 h1)))
let mac #i st l acc tag =
  admit();
  let h0 = ST.get () in
  poly1305_finish tag acc st.s;
  let h1 = ST.get () in
  if mac_log then
    begin
    //assume (mac_1305 l (sel_elem h0 st.r) (sel_word h0 st.s) ==
    //      little_endian (sel_word h1 tag));
    let t = read_word 16ul tag in
    m_recall #st.region #log #log_cmp (ilog st.log);
    assume (m_sel h1 (ilog st.log) == m_sel h0 (ilog st.log));
    m_write #st.region #log #log_cmp (ilog st.log) (Some (l, t))
    end
//16-09-24 why?

#set-options "--lax"

val verify: #i:id -> st:state i -> l:itext -> computed:accB i -> tag:tagB ->
  Stack bool
  (requires (fun h0 -> mac_log ==>
    sel_elem h0 computed == poly (reveal l) (sel_elem h0 st.r)))
  (ensures (fun h0 b h1 ->
    h0 == h1 /\
    (let mac = mac_1305 (reveal l) (sel_elem h0 st.r) (sel_word h0 st.s) in
     let verified = mac = sel_word h1 tag in
     let correct = HyperStack.sel h0 st.log = Some (l,mac) in
     b = verified && (not (authId i) || correct))))

let verify #i st l acc received =
  let tag = Buffer.create 0uy 16ul in
  poly1305_finish tag acc st.s;
  let verified = Buffer.eqb tag received 16ul in
  if mac_log && authId i then
    let st = !st.log in
    let correct = (st = Some(l,read_word 16ul tag)) in
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

 
// The code below is not internal to the idealization;
// it could go elsewhere, e.g. in AEAD.

// adapted from Poly1305.poly1305_update
val add:
  #i:id ->
  st: state i ->
  l0: itext ->
  a: accB i ->
  w:wordB_16 -> STL itext
  (requires (fun h -> acc_inv st l0 a h))
  (ensures (fun h0 l1 h1 ->
    modifies_1 a h0 h1 /\ 
    acc_inv st l1 a h1 /\
    (mac_log ==> reveal l1 = Seq.snoc (reveal l0) (encode (sel_word h0 w)))))

let add #i st l0 a w =
  push_frame();
  (* TODO: re-use the elem buffer rather that create a fresh one, maybe in the accumulator *)
  let e = Buffer.create 0UL Crypto.Symmetric.Poly1305.Parameters.nlength in
  toField_plus_2_128 e w;
  let l1 = update st l0 a e in
  let h = ST.get() in
//  let msg = esel_word h w in
//  let l1 = Ghost.elift2 (fun log msg -> Seq.snoc log (encode_16 msg)) l0 msg in
  pop_frame();
  l1
