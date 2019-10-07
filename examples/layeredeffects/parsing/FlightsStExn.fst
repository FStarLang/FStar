module FlightsStExn

open FStar.Integers

open FStar.HyperStack.ST

module HS = FStar.HyperStack

module B = LowStar.Buffer

open Messages
open MExn

noeq
type state = {
  b  : B.buffer uint_8;
  id : i:uint_32{i <= B.len b}
}

(*** Layering state on exception ***)

type pre_t = state -> HS.mem -> Type0
type post_t (a:Type) = option (a & state) -> HS.mem -> Type0
type wp_t0 (a:Type) = post_t a -> pre_t

unfold
let monotonic_wp (#a:Type) (wp:wp_t0 a) : Type0 =
  forall p q.
    (forall r h. p r h ==> q r h) ==>
    (forall st h. wp p st h ==> wp q st h)

type wp_t (a:Type) = wp:(post_t a -> pre_t){monotonic_wp wp}

inline_for_extraction
type mrepr (a:Type) (wp:wp_t a) =
  st:state -> EXN (a & state) (fun p h -> wp p st h)


inline_for_extraction noextract
let return (a:Type) (x:a)
: mrepr a (fun p st h -> p (Some (x, st)) h)
= fun st -> (x, st)

open FStar.Tactics

let lemma_monotonic
  (#a:Type) (#b:Type)
  (wp_f:wp_t a) (wp_g:a -> wp_t b)
  (post_a:(a:Type -> b:Type -> wp_g:(a -> wp_t b) -> p:post_t b -> post_t a))
  (p:post_t b) (q:post_t b) (st:state) (h:HS.mem)
: Lemma
  (requires forall (r:option (a & state)) (h:HS.mem). (post_a a b wp_g p) r h ==> (post_a a b wp_g q) r h)
  (ensures wp_f (post_a a b wp_g p) st h ==> wp_f (post_a a b wp_g q) st h)
= ()

unfold
let post_a (a:Type) (b:Type) (wp_g:a -> wp_t b) (p:post_t b) : post_t a =
  fun r h ->
  match r with
  | None -> p None h
  | Some r -> Prims.auto_squash (wp_g (Mktuple2?._1 r) p (Mktuple2?._2 r) h)

unfold
let bind_wp0 (#a:Type) (#b:Type) (wp_f:wp_t a) (wp_g:a -> wp_t b) : wp_t0 b =
  fun p -> wp_f (post_a a b wp_g p)

unfold
let bind_wp (#a:Type) (#b:Type) (wp_f:wp_t a) (wp_g:a -> wp_t b) : wp_t b
= assert (monotonic_wp (bind_wp0 wp_f wp_g)) by
    (norm [delta_only [`%monotonic_wp; `%bind_wp0]];
     (ignore (repeatn 5 l_intro));
     let wp_f, wp_g =
       match (cur_binders ()) with
       | _::_::wp_f::wp_g::_ -> wp_f, wp_g
       | _ -> fail "" in
     apply_lemma (`(lemma_monotonic
       (`#(binder_to_term wp_f))
       (`#(binder_to_term wp_g))
       post_a));
     norm [delta_only [`%post_a]]);
  bind_wp0 wp_f wp_g

inline_for_extraction noextract
let bind (a:Type) (b:Type)
  (wp_f:wp_t a) (wp_g:a -> wp_t b)
  (f:mrepr a wp_f) (g:(x:a -> mrepr b (wp_g x)))
: mrepr b (bind_wp wp_f wp_g)
= fun st ->
  let (x, st) = f st in
  g x st

inline_for_extraction noextract
let stronger (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:mrepr a wp_f)
: Pure (mrepr a wp_g)
  (requires forall p st h. wp_g p st h ==> wp_f p st h)
  (ensures fun _ -> True)
= f

inline_for_extraction noextract
let conjunction (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:mrepr a wp_f) (g:mrepr a wp_g)
  (p:Type0)
: Type
= mrepr a
  (fun post st h ->
    (p ==> wp_f post st h) /\
    (( ~p) ==> wp_g post st h))


reifiable reflectable
layered_effect {
  STEXN : a:Type -> wp_t a -> Effect
  with
  repr = mrepr;
  return = return;
  bind = bind;
  stronger = stronger;
  conjunction = conjunction
}

inline_for_extraction noextract
let lift_div_stexn (a:Type) (wp:pure_wp a{forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)}) (f:unit -> DIV a wp)
: mrepr a (fun p st h -> wp (fun x -> p (Some (x, st)) h))
= fun st -> (f (), st)

sub_effect DIV ~> STEXN = lift_div_stexn


effect StExn (a:Type) (pre:state -> HS.mem -> Type0) (post:state -> HS.mem -> option (a & state) -> HS.mem -> Type) =
  STEXN a (fun p st h -> pre st h /\ (forall r h1. (equal_stack_domains h h1 /\ post st h r h1) ==> p r h1))

type repr (a:Type0) = {
  v       : a;
  m_begin : uint_32;
  m_end   : uint_32
}

let valid_repr (#a:Type0) (b:B.buffer uint_8) (h:HS.mem) (r:repr a) : Type0
= valid_parsing b r.m_begin r.m_end h r.v

unfold let pre_m (st:state) (h:HS.mem) = B.live h st.b

unfold let post_m (#a:Type0) (st:state) (h0:HS.mem) (r:option (repr a & state)) (h1:HS.mem) =
  B.(modifies loc_none h0 h1) /\
  (match r with
   | None -> True
   | Some (x, st1) ->
     st1.b == st.b /\
     x.m_begin == st.id /\
     x.m_end == st1.id /\
     valid_repr #a st1.b h1 x)

inline_for_extraction noextract
let parse_common_ (#a:Type0)
  (parser:parser_t a)
  (_:unit)
  (st:state)
  (_:unit)
: ST (option (repr a & state)) (requires pre_m st) (ensures post_m st)
= let r = parser st.b st.id in
  match r with
  | None -> None
  | Some (x, m_end) -> Some ({ v = x; m_begin = st.id; m_end = m_end }, { st with id = m_end })

inline_for_extraction noextract
let parse_common_exn (#a:Type0)
  (parser:parser_t a)
  (_:unit)
  (st:state)
: Exn (repr a & state) (requires pre_m st) (ensures post_m st)
= EXN?.reflect (parse_common_ #a parser () st)

inline_for_extraction noextract
let parse_common (#a:Type0)
  (parser:parser_t a)
  (_:unit)
: StExn (repr a) (requires pre_m) (ensures post_m)
= STEXN?.reflect (parse_common_exn #a parser ())

noeq
type flt = {
  t1_msg : repr t1;
  t2_msg : repr t2;
  t3_msg : repr t3
}


inline_for_extraction noextract
let parse_t1 = parse_common #t1 t1_parser

inline_for_extraction noextract
let parse_t2 = parse_common #t2 t2_parser

inline_for_extraction noextract
let parse_t3 = parse_common #t3 t3_parser

inline_for_extraction noextract
let parse_flt_aux ()
: StExn flt
  (fun st h -> B.live h st.b)
  (fun st h0 r h1 ->
    B.(modifies loc_none h0 h1) /\
    (match r with
     | None -> True
     | Some (flt, _) ->
       valid_repr st.b h1 flt.t1_msg /\ valid_repr st.b h1 flt.t2_msg /\ valid_repr st.b h1 flt.t3_msg))
= let x = parse_t1 () in
  let y = parse_t2 () in
  let z = parse_t3 () in
  { t1_msg = x; t2_msg = y; t3_msg = z }

let parse_flt (b:B.buffer uint_8) (f_begin:uint_32) (f_end:uint_32)
: ST (option (flt & state))
  (requires fun h -> B.live h b /\ valid_indices b f_begin f_end)
  (ensures fun h0 r h1 ->
    B.(modifies loc_none h0 h1) /\
    (match r with
     | None -> True
     | Some (flt, _) -> valid_repr b h1 flt.t1_msg /\ valid_repr b h1 flt.t2_msg /\ valid_repr b h1 flt.t3_msg))
= reify (reify (parse_flt_aux ()) ({ b = b; id = f_begin })) ()
