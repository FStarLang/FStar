(*
   Copyright 2026 Microsoft Research

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
module Pulse.Extrinsic.Atomic

(** Unwrap native action semantics only inside this bridge. Open/close are
    extensionally memory-preserving, so bracketing an action does not change
    its physical correspondence. wp_atomic then turns a realizing action into
    WP, aging once only when the action has not already lowered the level.
    Native invariant allocation and later elimination are exposed separately
    for the mask-update calculus; neither introduces an invariant axiom. *)
friend PulseCore.Masks
friend PulseCore.InstantiatedSemantics
friend PulseCore.IndirectionTheoryActions

open FStar.Ghost
module L = Pulse.Extrinsic.Language
module W = Pulse.Extrinsic.WP
module R = Pulse.Extrinsic.Rules
module S = PulseCore.IndirectionTheorySep
module M = PulseCore.Masks
module IA = PulseCore.IndirectionTheoryActions
module O = PulseCore.Observability

let run #a #o #before #after #p #q f frame m =
  S.sep_laws ();
  f frame m

let native #a #mask #p #q f =
  S.sep_laws ();
  f

let run_native #a #mask #p #q f frame m = ()

let open_invariant mask i p = M.ghost_to_action (M.open_invariant mask i p)
let close_invariant mask i p = M.ghost_to_action (M.close_invariant mask i p)

let with_invariant #a mask i p pre post f =
  S.sep_laws ();
  fun frame m ->
    let _, opened = run (open_invariant mask i p) (S.star pre frame) m in
    let x, next = run f (S.star (S.inv i p) frame) opened in
    let _, closed = run (close_invariant mask i p) (S.star (post x) frame) next in
    x, closed

let open_unchanged (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)})
  (p frame:S.slprop) (m:S.full_mem{
    S.budget m >= 0 /\ S.inames_ok mask m /\
    S.interp (S.star (S.star (S.inv i p) frame) (S.mem_invariant mask m)) m })
  : Lemma ((run (open_invariant mask i p) frame m)._2 == m)
  = S.sep_laws ();
    assert_norm (((reveal (M.open_invariant mask i p)) frame m)._2 == m);
    assert_norm ((run (open_invariant mask i p) frame m)._2 ==
      S.update_ghost m (hide (((reveal (M.open_invariant mask i p)) frame m)._2)))

let close_unchanged (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)})
  (p frame:S.slprop) (m:S.full_mem{
    S.budget m >= 0 /\ S.inames_ok (S.add_inv mask i) m /\
    S.interp (S.star (S.star (S.star (S.inv i p) (exposed p)) frame)
      (S.mem_invariant (S.add_inv mask i) m)) m })
  : Lemma ((run (close_invariant mask i p) frame m)._2 == m)
  = S.sep_laws ();
    assert_norm (((reveal (M.close_invariant mask i p)) frame m)._2 == m);
    assert_norm ((run (close_invariant mask i p) frame m)._2 ==
      S.update_ghost m (hide (((reveal (M.close_invariant mask i p)) frame m)._2)))

(** Prove equality of the bracketed and unbracketed runs. This permits reuse
    of the primitive correspondence under an invariant, with its handle framed
    across the body and its exposed assertion restored before closing. *)
let with_invariant_run (#a:Type0) (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)})
  (p pre:S.slprop) (post:a -> S.slprop)
  (f:M.action a O.Observable (S.add_inv mask i) (S.add_inv mask i)
    (S.star (exposed p) pre) (exposed_post p post))
  (frame:S.slprop) (m:S.full_mem)
  : Lemma
      (requires enabled mask (S.star (S.inv i p) pre) frame m)
      (ensures
        enabled (S.add_inv mask i) (S.star (exposed p) pre) (S.star (S.inv i p) frame) m /\
        ((run (with_invariant mask i p pre post f) frame m) <: (a & S.full_mem)) ==
          ((run f (S.star (S.inv i p) frame) m) <: (a & S.full_mem)))
  = S.sep_laws ();
    open_unchanged mask i p (S.star pre frame) m;
    let _, opened = run (open_invariant mask i p) (S.star pre frame) m in
    let x, next = run f (S.star (S.inv i p) frame) m in
    close_unchanged mask i p (S.star (post x) frame) next

let realizes_with_invariant #a l physical e decode mask i p pre post f =
  introduce forall frame (m:S.full_mem).
    enabled mask (S.star (S.inv i p) pre) frame m ==>
    (let x, m' = run (with_invariant mask i p pre post f) frame m in
     S.level m' <= S.level m /\
     (S.level m' == S.level m ==> S.budget m' >= S.budget m) /\
     L.reducible l e (physical m) /\
     (forall e' s' spawned.
       l.L.prim_step e (physical m) e' s' spawned ==>
       l.L.to_val e' == Some (decode x) /\ s' == physical m' /\ spawned == []))
  with (
    if enabled mask (S.star (S.inv i p) pre) frame m then
      with_invariant_run mask i p pre post f frame m
  )

let wp_atomic l physical e p q f =
  S.sep_laws ();
  W.children_nil l (W.wp_family l physical);
  W.wp_lift l physical p e q (fun frame m ->
    S.inames_ok_empty m;
    let v, next = run f frame m in
    let result =
      if S.level next < S.level m then next
      else (
        R.age_resources (S.star (q v) frame) next;
        S.age_mem next
      )
    in
    assert (physical result == physical next);
    introduce forall e' s' spawned.
      l.L.prim_step e (physical m) e' s' spawned ==>
      (exists (m':S.full_mem).
        physical m' == s' /\ S.level m' < S.level m /\
        S.budget m' >= S.budget m - 1 /\
        S.interp (S.star (W.wp l physical e' q)
          (S.star (W.children l (W.wp_family l physical) spawned)
            (S.star frame (W.invariant m')))) m')
    with (
      introduce l.L.prim_step e (physical m) e' s' spawned ==>
        (exists (m':S.full_mem).
          physical m' == s' /\ S.level m' < S.level m /\
          S.budget m' >= S.budget m - 1 /\
          S.interp (S.star (W.wp l physical e' q)
            (S.star (W.children l (W.wp_family l physical) spawned)
              (S.star frame (W.invariant m')))) m')
      with (
        W.wp_value l physical e' v q;
        introduce exists (m':S.full_mem).
          physical m' == s' /\ S.level m' < S.level m /\
          S.budget m' >= S.budget m - 1 /\
          S.interp (S.star (W.wp l physical e' q)
            (S.star (W.children l (W.wp_family l physical) spawned)
              (S.star frame (W.invariant m')))) m'
        with result and ()
      )
    ))

let allocate_invariant p frame m =
  S.sep_laws ();
  S.inames_ok_empty m;
  let i, next = IA.new_invariant Pulse.Lib.GhostSet.empty p frame m in
  let (| _, fresh |) = S.fresh_inv p m Pulse.Lib.GhostSet.empty in
  S.disjoint_join_levels m fresh;
  assert_norm (next == S.join_mem m fresh);
  (| i, next |)

(** Aging lowers level; spending the supplied credit offsets that decrease in
    budget = level - credits - 1. This is not free credit generation. *)
let eliminate_later mask p frame m =
  S.sep_laws ();
  S.destruct_star_l (S.later_credit 1)
    (S.star (S.later p) (S.star frame (S.mem_invariant mask m))) m;
  S.interp_later_credit 1 m;
  S.age_level m;
  S.spend_lemma (S.age_mem m);
  let _, next = IA.later_elim mask p frame m in
  assert_norm (next == S.spend_mem (S.age_mem m));
  next
