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

type wp_t0 (a:Type) =
  wp:(post_t a -> pre_t)

unfold
let monotonic_wp (#a:Type) (wp:wp_t0 a) : Type0 =
  forall p q.
    (forall r h. p r h ==> q r h) ==>
    (forall st h. wp p st h ==> wp q st h)


type wp_t (a:Type) =
  wp:(post_t a -> pre_t){monotonic_wp wp}

type repr (a:Type) (wp:wp_t a) =
  st:state -> EXN (a & state) (fun p h -> wp p st h)


let return (a:Type) (x:a)
: repr a (fun p st h -> p (Some (x, st)) h)
= fun st -> (x, st)

unfold
let post_a (a:Type) (b:Type) (wp_g:a -> wp_t b) (p:post_t b) : post_t a =
  fun r h ->
  match r with
  | None -> p None h
  | Some r -> Prims.auto_squash (wp_g (Mktuple2?._1 r) p (Mktuple2?._2 r) h)

let lemma_monotonic2 (#a:Type) (#b:Type) (wp_f:wp_t a) (wp_g:a -> wp_t b) (p:post_t b) (q:post_t b) (st:state) (h:HS.mem)
: Lemma
  (requires forall (r:option (a & state)) (h:HS.mem). (post_a a b wp_g p) r h ==> (post_a a b wp_g q) r h)
  (ensures wp_f (post_a a b wp_g p) st h ==> wp_f (post_a a b wp_g q) st h)
= let aux (p q:post_t a)
    : Lemma ((forall r h. p r h ==> q r h) ==> (forall st h. wp_f p st h ==> wp_f q st h))
    = () in
  aux (post_a a b wp_g p) (post_a a b wp_g q);
  admit ()

unfold
let bind_wp0 (a:Type) (b:Type) (wp_f:wp_t a) (wp_g:a -> wp_t b) : post_t b -> pre_t =
  fun p st h -> wp_f (post_a a b wp_g p) st h

open FStar.Tactics

unfold
let bind_wp (a:Type) (b:Type) (wp_f:wp_t a) (wp_g:a -> wp_t b) : wp_t b
= assert (monotonic_wp (bind_wp0 a b wp_f wp_g)) by
    (norm [delta_only [`%monotonic_wp]];
     let p_binder = forall_intro () in
     let q_binder = forall_intro () in
     ignore (implies_intro ());
     ignore (forall_intro ());
     norm [delta_only [`%bind_wp0]];
     ignore (forall_intro ());
     let wp_f_binder, wp_g_binder =
       match (cur_binders ()) with
       | _::_::wp_f::wp_g::_ -> wp_f, wp_g
       | _ -> fail "" in
     apply_lemma (`(lemma_monotonic2 (`#(binder_to_term wp_f_binder)) (`#(binder_to_term wp_g_binder)) (`#(binder_to_term p_binder)) (`#(binder_to_term q_binder))));
     norm [delta_only [`%post_a]];
     ignore (forall_intro ()));
  bind_wp0 a b wp_f wp_g

inline_for_extraction
let bind (a:Type) (b:Type)
  (wp_f:wp_t a) (wp_g:a -> wp_t b)
  (f:repr a wp_f) (g:(x:a -> repr b (wp_g x)))
: repr b (bind_wp a b wp_f wp_g)
= fun st ->
  let (x, st) = f st in
  g x st


type repr (a:Type0) = {
  v       : a;
  m_begin : uint_32;
  m_end   : uint_32
}

let valid_repr (#a:Type0) (b:B.buffer uint_8) (h:HS.mem) (r:repr a) : Type0
= valid_parsing b r.m_begin r.m_end h r.v


noeq
type flt = {
  t1_msg : repr t1;
  t2_msg : repr t2;
  t3_msg : repr t3
}


unfold let pre_m (b:B.buffer uint_8) m_begin =
  fun h -> B.live h b /\ m_begin <= B.len b

unfold let post_m (#a:Type0) b =
  fun h0 r h1 ->
  B.(modifies loc_none h0 h1) /\
  (match r with
   | None -> True
   | Some x -> valid_repr b h1 x)

inline_for_extraction
let parse_common_ (#a:Type0)
  (parser:parser_t a)
  (b:B.buffer uint_8)
  (m_begin:uint_32)
: unit -> ST (option (repr a)) (requires pre_m b m_begin) (ensures post_m #a b)
= fun _ ->
  let r = parser b m_begin in
  match r with
  | None -> None
  | Some (x, m_end) -> Some ({ v = x; m_begin = m_begin; m_end = m_end })

inline_for_extraction
let parse_common (#a:Type0) (parser:parser_t a) (b:B.buffer uint_8) (m_begin:uint_32)
: Exn (repr a) (requires pre_m b m_begin) (ensures post_m #a b)
= EXN?.reflect (parse_common_ #a parser b m_begin)

inline_for_extraction
let parse_t1 = parse_common #t1 t1_parser

inline_for_extraction
let parse_t2 = parse_common #t2 t2_parser

inline_for_extraction
let parse_t3 = parse_common #t3 t3_parser

unfold let pre_f (b:B.buffer uint_8) f_begin f_end =
  fun h -> B.live h b /\ valid_indices b f_begin f_end

unfold let post_f (b:B.buffer uint_8) =
  fun h0 r h1 ->
   B.(modifies loc_none h0 h1) /\
   (match r with
    | None -> True
    | Some flt -> valid_repr b h1 flt.t1_msg /\ valid_repr b h1 flt.t2_msg /\ valid_repr b h1 flt.t3_msg)

inline_for_extraction
let parse_flt_aux (b:B.buffer uint_8) (f_begin:uint_32) (f_end:uint_32)
: Exn flt (requires pre_f b f_begin f_end) (ensures post_f b)
= let x = parse_t1 b f_begin in
  let y = parse_t2 b x.m_end in
  let z = parse_t3 b y.m_end in
  { t1_msg = x;
    t2_msg = y;
    t3_msg = z }

let parse_flt (b:B.buffer uint_8) (f_begin:uint_32) (f_end:uint_32)
: ST (option flt) (requires pre_f b f_begin f_end) (ensures post_f b)
= reify (parse_flt_aux b f_begin f_end) ()
