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
open FStar.HST.Monotonic.RRef

open Crypto.Symmetric.Poly1305.Spec
open Crypto.Symmetric.Poly1305 // avoid?

module HH = FStar.HyperHeap

let norm = Crypto.Symmetric.Poly1305.Bigint.norm 


// also used in miTLS ('model' may be better than 'ideal'); could be loaded from another module.
// this flag enables conditional idealization by keeping additional data,
// - this should not affect the code behavior
// - this may cause the code not to compile to Kremlin/C.
assume val ideal: bool
//let ideal = true

// to be rewired. 
// In AEAD_ChaCha20: id * nonce
// we will need authId i ==> ideal?
assume new abstract type id
assume val authId: id -> Tot bool
assume val someId: id
(*
type id = nat
let authId i = false
let someId = 0
*)

type bytes = buffer UInt8.t
type lbytes (n:nat) = b:bytes{length b = n}
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

val random: r:rid -> len:UInt32.t -> ST bytes
     (requires (fun h -> is_eternal_region r))
     (ensures (fun (h0:mem) b h1 ->
	 ~(contains h0 b)
       /\ live h1 b /\ idx b = 0 /\ length b = UInt32.v len
       /\ Map.domain h1.h == Map.domain h0.h
       /\ h1.tip = h0.tip
       /\ modifies (Set.singleton r) h0 h1
       /\ modifies_ref r TSet.empty h0 h1))

// TODO: dummy, implement properly
let random r len = FStar.Buffer.rcreate r 0uy len


type log = option (text * tag) // option (Seq.seq elem * word16)

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

let log_ref (r:rid) = if ideal then ideal_log r else unit

let ilog (#r:rid) (l:log_ref r{ideal}) : Tot (ideal_log r) = l

// the sequence of hashed elements is conditional, but not ghost
// this will require changing e.g. the type of poly1305_add
let itext : Type0 = if ideal then text else unit

let text_0: itext = if ideal then Seq.createEmpty #elem else ()

noeq type state (i:id) =
  | State:
      #region: rid ->
      r: elemB ->
      s: wordB_16 ->
      log: log_ref region ->
      state i


val alloc: i:id
  -> region:rid{is_eternal_region region}
  -> key:bytes{length key >= 32}
  -> ST (state i)
  (requires (fun m0 -> live m0 key))
  (ensures  (fun m0 st m1 ->
    ~(contains m0 st.r) /\
    ~(contains m0 st.s) /\
    //modifies (Set.singleton region) m0 m1 /\ // Can't prove this
    st.region == region /\
    (ideal ==> m_contains (ilog st.log) m1 /\ m_sel m1 (ilog st.log) == None)
  ))

let alloc i region key =
  let r = FStar.Buffer.rcreate region 0UL 5ul in
  let s = FStar.Buffer.rcreate region 0uy 16ul in
  cut (disjoint r key /\ disjoint s key);
  poly1305_init r s key;
  if ideal then
    let log = m_alloc #log #log_cmp region None in
    State #i #region r s log
  else
    State #i #region r s ()


val gen: i:id
  -> region:rid{is_eternal_region region}
  -> ST (state i)
  (requires (fun m0 -> True))
  (ensures  (fun m0 st m1 ->
    ~(contains m0 st.r) /\
    ~(contains m0 st.s) /\
    //modifies (Set.singleton r) m0 m1
    st.region == region /\
    (ideal ==> m_contains (ilog st.log) m1 /\ m_sel m1 (ilog st.log) == None)))

let gen i region =
  let key = random region 32ul in
  alloc i region key


val coerce: i:id{~(authId i)} -> r:rid -> key:lbytes 32 -> ST (state i)
  (requires (fun m0 -> live m0 key))
  (ensures  (fun m0 st m1 ->
    //modifies (Set.singleton r) m0 m1 /\
    (ideal ==> m_contains (ilog st.log) m1 /\ m_sel m1 (ilog st.log) == None)))

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

let acc_inv (#i:id) (st:state i) (l:itext) (a:accB i) h =
  live h st.r /\ live h a /\ disjoint st.r a /\   
  norm h st.r /\ norm h a /\
  (let r = sel_elem h st.r in
   let a = sel_elem h a in
   ideal ==> a = poly l r)


// not framed, as we allocate private state on the caller stack
val start: #i:id -> st:state i -> StackInline (accB i)
  (requires (fun h -> is_stack_region h.tip /\ live h st.r /\ norm h st.r))
  (ensures  (fun h0 a h1 -> acc_inv st text_0 a h1))
let start #i st = 
  let h0 = HST.get () in
  let a = Buffer.create 0UL 5ul in
  let h1 = HST.get () in
  lemma_reveal_modifies_0 h0 h1;
  cut (equal h0 st.r h1 st.r);
  poly1305_start a;
  let h2 = HST.get () in
  lemma_reveal_modifies_1 a h1 h2;
  cut (equal h1 st.r h2 st.r);
  Bigint.norm_eq_lemma h0 h2 st.r st.r;
  a

// CHECKPOINT

val update: #i:id -> st:state i -> l:itext -> a:accB i -> v:elemB -> ST itext
  (requires (fun h0 -> // "liveness" /\ 
    acc_inv st l a h0))
  (ensures (fun h0 l1 h1 -> 
    modifies_1 a h0 h1 /\
//?    (ideal ==> l1 = FStar.SeqProperties.snoc l (sel_elem h1 v)) /\
    acc_inv st l1 a h1 ))
    
let update #i st vs a v = 
  assume false; //TODO
  add_and_multiply a v st.r 


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

val mac: #i:id -> st:state i -> l:itext -> computed:accB i -> tag: tagB -> ST unit
  (requires (fun h0 -> ideal ==> 
    sel_elem h0 l = poly l (sel_elem h0 st.r)  /\
    m_sel h0 (ilog st.log) == None))
  (ensures (fun h0 _ h1 -> live h0 st.s /\
    // modifies h0 h1 "the tag buffer and st.log" /\ 
    (let s: word_16 = sel_word h0 st.s in
    let mac = mac_1305 l (sel_elem h0 st.r) s in
    mac = little_endian (sel_word h1 tag) /\
    (ideal /\ authId i ==> m_sel h1 (ilog st.log) == Some (l,sel_word h1 tag)))))

let mac #i st vs acc tag = 
  poly1305_finish tag acc st.s;
  if ideal then st.log := (Some (vs,read_word tag))


val verify: #i:id -> st:state i -> l:itext -> computed:accB i -> tag: tagB -> 
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
  let verified = Buffer.eqb tag received 16ul in
  if ideal && authId i then 
    let st = !st.log in 
    let correct = (st = Some(l,read_word tag)) in
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


// The code below is not involved in the idealization;
// it could go elsewhere, e.g. in AEAD.

// adapted from Poly1305.poly1305_update
val add:
  #i:id ->
  st: state i ->
  l0: itext -> 
  a: accB i ->
  w:wordB_16 -> STL itext
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
  let l1 = Ghost.elift2 (fun log msg -> SeqProperties.snoc log (encode_16 msg)) l0 msg in
  pop_frame();
  l1

let sel_bytes (h:mem) (b:bytes{live h b}) : GTot (Seq.seq UInt8.t) = as_seq h b


// a spec for encoding and padding, convenient for injectivity proof

let pad_0 b l = Seq.append b (Seq.create l 0uy)

val encode_pad: Seq.seq elem -> Seq.seq UInt8.t -> GTot (Seq.seq elem)

let rec encode_pad prefix txt = 
  let l = Seq.length txt in
  if l = 0 then prefix
  else if l < 16 then 
    begin
      let w = pad_0 txt (16 - l) in
      SeqProperties.snoc prefix (encode_16 w)
    end
  else 
    begin
      let w = Seq.slice txt 0 16 in
      let txt = Seq.slice txt 16 l in 
      let prefix = SeqProperties.snoc prefix (encode_16 w) in
      encode_pad prefix txt 
    end


val lemma_encode_pad_injective: p0:_ -> t0:_ -> p1:_ -> t1:_ -> Lemma
  (requires 
     p0 = p1 /\
     Seq.length t0 = Seq.length t1 /\
     encode_pad p0 t0 = encode_pad p1 t1) 
  (ensures t0 = t1)

//TODO
let lemma_encode_pad_injective p0 t0 p1 t1 = 
  let l = Seq.length t0 in 
  if l = 0 then assume false else
  if l < 16 then assume false
  else assume false
