(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module FlightsStExn

/// Continuing the flights parsing example,
///   if you see the `parse_flt_aux` function in FlightsExn.fst,
///   the code is still stitching the indices, passing around the buffer, etc.
///
/// But that can also be encapsulated in a state effect
///
/// This module layers a state effect over Exn


open FStar.Integers

open FStar.HyperStack.ST

module HS = FStar.HyperStack

module B = LowStar.Buffer

open Messages
open MExn

module M = Messages



/// Layering state on top of EXN


type pre_t (state:Type0) = state -> HS.mem -> Type0
type post_t (state:Type0) (a:Type) = option (a & state) -> HS.mem -> Type0
type wp_t0 (state:Type0) (a:Type) = post_t state a -> pre_t state

/// Require the wp to be monotonic

unfold
let monotonic_wp (#state:Type0) (#a:Type) (wp:wp_t0 state a) : Type0 =
  forall p q.
    (forall r h. p r h ==> q r h) ==>
    (forall st h. wp p st h ==> wp q st h)

type wp_t (state:Type0) (a:Type) = wp:(post_t state a -> pre_t state){monotonic_wp wp}


/// Underlying representation in terms of EXN


inline_for_extraction
type mrepr (a:Type) (state:Type0) (wp:wp_t state a) =
  st:state -> EXN (a & state) (fun p h -> wp p st h)


/// Effect combinators

inline_for_extraction noextract
let return (a:Type) (state:Type0) (x:a)
: mrepr a state (fun p st h -> p (Some (x, st)) h)
= fun st -> (x, st)


/// Some hard work to convince Z3 that the `bind_wp` is monotonic

open FStar.Tactics

let lemma_monotonic
  (#a:Type) (#b:Type) (#state:Type0)
  (wp_f:wp_t state a) (wp_g:a -> wp_t state b)
  (post_a:(#a:Type -> #b:Type -> #state:Type0 -> wp_g:(a -> wp_t state b) -> p:post_t state b -> post_t state a))
  (p:post_t state b) (q:post_t state b) (st:state) (h:HS.mem)
: Lemma
  (requires forall (r:option (a & state)) (h:HS.mem). (post_a wp_g p) r h ==> (post_a wp_g q) r h)
  (ensures wp_f (post_a wp_g p) st h ==> wp_f (post_a wp_g q) st h)
= ()

unfold
let post_a (#a:Type) (#b:Type) (#state:Type0) (wp_g:a -> wp_t state b) (p:post_t state b) : post_t state a =
  fun r h ->
  match r with
  | None -> p None h
  | Some r -> Prims.auto_squash (wp_g (Mktuple2?._1 r) p (Mktuple2?._2 r) h)

unfold
let bind_wp0 (#a:Type) (#b:Type) (#state:Type0) (wp_f:wp_t state a) (wp_g:a -> wp_t state b) : wp_t0 state b =
  fun p -> wp_f (post_a wp_g p)

unfold
let bind_wp (#a:Type) (#b:Type) (#state:Type0) (wp_f:wp_t state a) (wp_g:a -> wp_t state b) : wp_t state b
= assert (monotonic_wp (bind_wp0 wp_f wp_g)) by
    (norm [delta_only [`%monotonic_wp; `%bind_wp0]];
     ignore (repeatn 5 l_intro);
     let wp_f, wp_g =
       match (cur_binders ()) with
       | _::_::_::wp_f::wp_g::_ -> wp_f, wp_g
       | _ -> fail "" in
     apply_lemma (`(lemma_monotonic
       (`#(binder_to_term wp_f))
       (`#(binder_to_term wp_g))
       post_a));

     norm [delta_only [`%post_a]]);
  bind_wp0 wp_f wp_g

inline_for_extraction noextract
let bind (a:Type) (b:Type)
  (state:Type0)
  (wp_f:wp_t state a) (wp_g:a -> wp_t state b)
  (f:mrepr a state wp_f) (g:(x:a -> mrepr b state (wp_g x)))
: mrepr b state (bind_wp wp_f wp_g)
= fun st ->
  let (x, st) = f st in
  g x st

inline_for_extraction noextract
let subcomp (a:Type)
  (state:Type0)
  (wp_f:wp_t state a) (wp_g:wp_t state a)
  (f:mrepr a state wp_f)
: Pure (mrepr a state wp_g)
  (requires forall p st h. wp_g p st h ==> wp_f p st h)
  (ensures fun _ -> True)
= f

inline_for_extraction noextract
let if_then_else (a:Type)
  (state:Type0)
  (wp_f:wp_t state a) (wp_g:wp_t state a)
  (f:mrepr a state wp_f) (g:mrepr a state wp_g)
  (p:Type0)
: Type
= mrepr a state
  (fun post st h ->
    (p ==> wp_f post st h) /\
    (( ~p) ==> wp_g post st h))


reifiable reflectable
layered_effect {
  STEXN : a:Type -> state:Type0 -> wp_t state a -> Effect
  with
  repr = mrepr;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}


/// Lift from DIV (on monotonic wps)

inline_for_extraction noextract
let lift_div_stexn (a:Type) (state:Type0) (wp:pure_wp a{forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)}) (f:unit -> DIV a wp)
: mrepr a state (fun p st h -> wp (fun x -> p (Some (x, st)) h))
= fun st -> (f (), st)

sub_effect DIV ~> STEXN = lift_div_stexn


/// Hoare-style abbreviation


/// Type of the state

noeq
type rcv_state = {
  b  : B.buffer uint_8;
  id : i:uint_32{i <= B.len b}
}


effect StExn (a:Type) (pre:rcv_state -> HS.mem -> Type0) (post:rcv_state -> HS.mem -> option (a & rcv_state) -> HS.mem -> Type) =
  STEXN a rcv_state (fun p st h -> pre st h /\ (forall r h1. post st h r h1 ==> p r h1))


/// parse_common function, this time in terms of `StExn`


unfold let parse_common_wp (a:Type0) : wp_t rcv_state (M.repr a)
= fun p st h0 ->
  B.live h0 st.b /\
  (forall r h1.
     (B.(modifies loc_none h0 h1) ==>
     (match r with
      | None -> p None h1
      | Some (x, st1) -> (st1.b == st.b /\ x.m_begin == st.id /\ x.m_end == st1.id /\ valid_repr #a st1.b h1 x) ==> p r h1)))


inline_for_extraction noextract
let parse_common_ (#a:Type0)
  (parser:parser_t a)
  (_:unit)
  (st:rcv_state)
: MExn.repr (M.repr a & rcv_state) (fun p h0 -> parse_common_wp a p st h0)
= fun _ ->
  let r = parser st.b st.id in
  match r with
  | None -> None
  | Some (x, m_end) -> Some ({ v = x; m_begin = st.id; m_end = m_end }, { st with id = m_end })

inline_for_extraction noextract
let parse_common_exn (#a:Type0)
  (parser:parser_t a)
  (_:unit)
  (st:rcv_state)
: EXN (M.repr a & rcv_state) (fun p h0 -> parse_common_wp a p st h0)
= EXN?.reflect (parse_common_ #a parser () st)

inline_for_extraction noextract
let parse_common (#a:Type0)
  (parser:parser_t a)
  (_:unit)
: StExn (M.repr a)
  (requires fun st h -> B.live h st.b)
  (ensures fun st h0 r h1 ->
    B.live h1 st.b /\ B.(modifies loc_none h0 h1) /\
    (match r with
     | None -> True
     | Some (x, st1) -> st1.b == st.b /\ x.m_begin == st.id /\ x.m_end == st1.id /\ valid_repr #a st1.b h1 x))
= STEXN?.reflect (parse_common_exn #a parser ())


/// Partially applied functions

inline_for_extraction noextract
let parse_t1 = parse_common #t1 t1_parser

inline_for_extraction noextract
let parse_t2 = parse_common #t2 t2_parser

inline_for_extraction noextract
let parse_t3 = parse_common #t3 t3_parser


/// The flight parsing function

#set-options "--using_facts_from '* -LowStar -FStar.HyperStack -FStar.Monotonic -FStar.Heap'"

inline_for_extraction noextract
let parse_flt_aux ()
: StExn flt (fun st h -> pre_f st.b st.id h)
  (fun st h0 r h1 ->
   match r with
   | None -> post_f st.b h0 None h1
   | Some (x, _) -> post_f st.b h0 (Some x) h1)
= let x = parse_t1 () in
  let y = parse_t2 () in
  let z = parse_t3 () in
  { t1_msg = x; t2_msg = y; t3_msg = z }


/// The client-facing code can provide the same specs

let parse_flt : parse_flt_t
= fun b f_begin ->
  let r = reify (reify (parse_flt_aux ()) ({ b = b; id = f_begin })) () in
  match r with
  | None -> None
  | Some (x, _) -> Some x
