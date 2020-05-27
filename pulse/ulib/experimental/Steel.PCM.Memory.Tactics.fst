(*
   Copyright 2020 Microsoft Research

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

module Steel.PCM.Memory.Tactics

module M = Steel.PCM.Memory

/// Attribute for normalization
let __reduce__ = ()

unfold
let normal (#a:Type) (x:a) =
  let open FStar.Algebra.CommMonoid.Equiv in
  norm [delta_attr [`%__reduce__];
       delta;
        delta_only [
          `%__proj__CM__item__unit;
          `%__proj__CM__item__mult;
          `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
          `%fst; `%snd];
        primops; iota; zeta] x

open FStar.Algebra.CommMonoid.Equiv
open FStar.Tactics
open FStar.Tactics.CanonCommMonoidSimple.Equiv

let equiv_refl (x:M.slprop) : Lemma (M.equiv x x) = ()

let equiv_sym (x y:M.slprop) : Lemma
  (requires M.equiv x y)
  (ensures M.equiv y x)
  = ()

let equiv_trans (x y z:M.slprop) : Lemma
  (requires M.equiv x y /\ M.equiv y z)
  (ensures M.equiv x z)
  = ()

inline_for_extraction noextract let req : equiv M.slprop =
  EQ M.equiv
     equiv_refl
     equiv_sym
     equiv_trans

let cm_identity (x:M.slprop) : Lemma ((M.emp `M.star` x) `M.equiv` x)
  = M.star_commutative x M.emp;
    M.emp_unit x

[@@__reduce__]
inline_for_extraction noextract let rm : cm M.slprop req =
  CM M.emp
     M.star
     cm_identity
     M.star_associative
     M.star_commutative
     M.star_congruence

inline_for_extraction noextract let canon () : Tac unit =
  canon_monoid (`req) (`rm)

let can_be_split_into (outer inner delta:M.slprop) =
  (inner `M.star` delta) `M.equiv` outer

let squash_and p q (x:squash (p /\ q)) : (p /\ q) =
  let x : squash (p `c_and` q) = FStar.Squash.join_squash x in
  x


inline_for_extraction noextract let resolve_frame () : Tac unit =
  norm [delta_attr [`%__reduce__];
       delta;
        delta_only [
          `%__proj__CM__item__unit;
          `%__proj__CM__item__mult;
          `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
          `%fst; `%snd];
        primops; iota; zeta];
  refine_intro();
  flip();
  apply_lemma (`unfold_with_tactic);
  split();
  norm [delta_only [`%can_be_split_into]];
  canon();
  trivial()

inline_for_extraction noextract let reprove_frame () : Tac unit =
  norm [delta_attr [`%__reduce__];
       delta;
        delta_only [
          `%__proj__CM__item__unit;
          `%__proj__CM__item__mult;
          `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
          `%fst; `%snd];
        primops; iota; zeta];
  apply (`squash_and);
  norm [delta_only [`%can_be_split_into]];
  split();
  canon();
  trivial()

val shuffled (p : M.slprop)
             (q : M.slprop{with_tactic canon (squash (p `M.equiv` q))})
    : Lemma (p `M.equiv` q)

#push-options "--no_tactics" (* GM: This should not be needed *)
let shuffled p q =
  by_tactic_seman canon (squash (p `M.equiv` q))
#pop-options

(*** Small examples for frame inference ***)

#push-options "--no_tactics"

open Steel.PCM.Semantics.Instantiate
open Steel.PCM.Memory
module Mem = Steel.PCM.Memory
open Steel.PCM.Effect

assume
val rassert
  (#h_in:slprop)
  (h_out:slprop{
    FStar.Tactics.with_tactic
    reprove_frame
    (can_be_split_into h_in h_out emp /\ True)})
  : SteelT unit h_in (fun _ -> h_out)
  // = Steel?.reflect (fun _ ->
  //     let m0 = mst_get () in
  //     FStar.Tactics.by_tactic_seman reprove_frame (can_be_split_into h_in h_out emp /\ True);
  //     let (| _, m1 |) = rewrite_slprop h_in h_out m0 in
  //     act_preserves_frame_and_preorder (rewrite_slprop h_in h_out) m0;
  //     mst_put m1)

let steel_frame_t
  (#outer:slprop)
  (#a:Type) (#pre:slprop) (#post:a -> slprop)
  (#[resolve_frame()]
    frame:slprop{
      FStar.Tactics.with_tactic
      reprove_frame
      (can_be_split_into outer pre frame /\ True)}
  )
  ($f:unit -> Steel a pre post (fun _ -> True) (fun _ _ _ -> True))
: SteelT a
  outer
  (fun x -> post x `Mem.star` frame)
= FStar.Tactics.by_tactic_seman reprove_frame (can_be_split_into outer pre frame /\ True);
  Mem.emp_unit (pre `Mem.star` frame);
  FStar.Tactics.unfold_with_tactic reprove_frame
    (can_be_split_into outer (pre `Mem.star` frame) emp /\ True);
  rassert (pre `Mem.star` frame);
  Steel.PCM.SteelT.Basics.frame f frame
#pop-options

(* Some helpers *)
private
val reshuffle0 (#p #q : slprop)
              (_ : squash (p `equiv` q))
   : SteelT unit p (fun _ -> q)

private
let reshuffle0 #p #q peq =
  Steel.PCM.Effect.Atomic.lift_atomic_to_steelT
    (fun () -> Steel.PCM.Effect.Atomic.change_slprop p q (fun m -> ()))

module T = FStar.Tactics

val reshuffle (#p #q : slprop)
              (_ : squash (T.with_tactic canon
                                         (squash (p `equiv` q))))
   : SteelT unit p (fun _ -> q)

#push-options "--no_tactics" (* GM: This should not be needed *)

let reshuffle #p #q peq =
  T.by_tactic_seman canon (squash (p `equiv` q));
  reshuffle0 ()

#pop-options
