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
module PulseCore.Masks

(** Friend access exposes existing action representations only in this module,
keeping the abstraction boundary used by PulseCore.Atomic's proofs intact. *)

friend PulseCore.Action
friend PulseCore.InstantiatedSemantics

open FStar.Ghost
open PulseCore.InstantiatedSemantics
open PulseCore.Action
open PulseCore.Atomic
open PulseCore.Observability
open Pulse.Lib.Loc
module Sep = PulseCore.IndirectionTheorySep
module A = PulseCore.Action
module AT = PulseCore.Atomic

module H = PulseCore.HoareStateMonad
module IA = PulseCore.IndirectionTheoryActions

(** The ambient invariant assertion owns all bodies except those in the open
mask. Every step preserves an arbitrary frame and spends at most one unit of
semantic budget. Neutral steps preserve the budget and ghost-state relation. *)
let action (a:Type u#a) (obs:observability)
  (before after:inames) (pre:slprop) (post:a -> slprop)
  : Type u#(max 4 a)
  = frame:slprop ->
    H.st #Sep.full_mem a
      (fun m ->
        Sep.budget m >= 0 /\ (obs == Observable ==> Sep.budget m > 0) /\
        Sep.inames_ok before m /\
        Sep.interp (pre ** frame ** Sep.mem_invariant before m) m)
      (fun m0 x m1 ->
        Sep.budget m0 - Sep.budget m1 <= 1 /\
        (obs == Neutral ==> Sep.is_ghost_action m0 m1 /\ Sep.budget m0 == Sep.budget m1) /\
        Sep.inames_ok after m1 /\
        Sep.interp (post x ** frame ** Sep.mem_invariant after m1) m1)

let gaction a before after pre post =
  erased (action (erased a) Neutral before after pre (fun x -> post (reveal x)))

let return_action #a mask x post : action a Neutral mask mask (post x) post =
  fun frame m ->
    assert (FStar.Preorder.reflexive Sep.is_ghost_action);
    x, m

let bind_action #a #b #o1 #o2 #m1 #m2 #m3 #p #q #r f g
  : action b (join_obs o1 o2) m1 m3 p r =
  assert (FStar.Preorder.transitive Sep.is_ghost_action);
  fun frame m0 ->
    let x, m1 = f frame m0 in
    g x frame m1

let frame_action #a #o #m1 #m2 #p #q r f
  : action a o m1 m2 (p ** r) (fun x -> q x ** r) =
  Sep.sep_laws ();
  fun frame -> f (r ** frame)

let lift_atomic_action #a #o #opens #p #q mask f
  : action a o mask mask p q =
  let (| t, decode, step |) = AT.as_action f #mask in
  fun frame m0 ->
    let x, m1 = step frame m0 in
    decode x, m1

let lift_ghost_action #a #opens #p #q mask f
  : gaction a mask mask p q =
  hide (lift_atomic_action mask (AT.lift_ghost_neutral' f))

(** Replay only a valid ghost update. Revealing the erased witness cannot
manufacture a runtime result or change the concrete heap. *)
let ghost_to_action #a #m1 #m2 #p #q f
  : action (erased a) Neutral m1 m2 p (fun x -> q x) =
  fun frame m0 ->
    let result : erased (erased a & Sep.full_mem) = hide ((reveal f) frame m0) in
    let x : erased a = fst result in
    let m1 = Sep.update_ghost m0 (hide (snd result)) in
    x, m1

let bind_gaction #a #b #m1 #m2 #m3 #p #q #r f g
  : gaction b m1 m3 p r =
  hide (bind_action (ghost_to_action f) (fun x -> ghost_to_action (g (reveal x))))

let frame_gaction #a #m1 #m2 #p #q r f
  : gaction a m1 m2 (p ** r) (fun x -> q x ** r) =
  hide (frame_action r (ghost_to_action f))

let action_to_ghost #a #m1 #m2 #p #q f
  : gaction a m1 m2 p q =
  hide (fun frame m0 ->
    let x, m1 = f frame m0 in
    hide x, m1)

let sub_gaction #a #m1 #m2 #p #q p' q' f
  : gaction a m1 m2 p' q' =
  hide (fun frame m0 -> ghost_to_action f frame m0)

let reindex_gaction #a #m1 #m2 #p #q before after f = f

let localize_gaction #a #before #after #pre #post l
  (f:gaction a before after pre post)
  : gaction a before after (Sep.on l pre) (fun x -> Sep.on l (post x)) =
  let step : action (erased a) Neutral before after (Sep.on l pre)
      (fun x -> Sep.on l (post (reveal x))) =
    fun frame m0 ->
    Sep.sep_laws ();
    let l0 = Sep.current_loc m0 in
    let m1 = Sep.set_loc m0 l in
    A.impersonate_lem1 l m0 pre before frame;
    let x, m2 = ghost_to_action f (Sep.loc l ** Sep.on l0 frame) m1 in
    let m3 = Sep.set_loc m2 l0 in
    A.impersonate_lem2 l l0 m2 (post (reveal x)) after frame;
    assert (FStar.Preorder.transitive Sep.is_ghost_action);
    x, m3
  in hide step

let finish_gaction #a #m1 #m2 #p x post f =
  bind_action (ghost_to_action f) (fun _ -> return_action m2 x post)

let run_action #a #o #p #q opens f : stt_atomic a #o opens p q =
  AT.of_action (A.lift_pre_act0_act (fun #mask -> f mask))

let run_closed_action #a #o #p #q f
  : stt_atomic a #o (GhostSet.complement emp_inames) p q =
  run_action (GhostSet.complement emp_inames) (fun mask ->
    GhostSet.lemma_equal_intro mask emp_inames;
    f)

(** Opening and closing redistribute read_inv and the ambient invariant
resource without changing memory. Both locality and later are preserved. *)
let open_invariant mask i p
  : gaction unit mask (add_inv mask i)
      (inv i p) (fun _ -> inv i p ** Sep.somewhere (later p)) =
  let step : action (erased unit) Neutral mask (add_inv mask i)
      (inv i p) (fun _ -> inv i p ** Sep.somewhere (later p)) =
    fun frame m ->
    Sep.sep_laws ();
    Sep.destruct_star_l (inv i p) (frame ** Sep.mem_invariant mask m) m;
    Sep.inames_ok_single i p m;
    Sep.mem_invariant_equiv mask m i;
    IA.elim_read_inv i p (frame ** Sep.mem_invariant (add_inv mask i) m) m;
    Sep.inames_ok_union (Sep.single i) mask m;
    assert (FStar.Preorder.reflexive Sep.is_ghost_action);
    hide (), m
  in hide step

let close_invariant mask i p
  : gaction unit (add_inv mask i) mask
      (inv i p ** Sep.somewhere (later p)) (fun _ -> inv i p) =
  let step : action (erased unit) Neutral (add_inv mask i) mask
      (inv i p ** Sep.somewhere (later p)) (fun _ -> inv i p) =
    fun frame m ->
    Sep.sep_laws ();
    Sep.inames_ok_union (Sep.single i) mask m;
    Sep.destruct_star_l (inv i p)
      (Sep.somewhere (later p) ** frame ** Sep.mem_invariant (add_inv mask i) m) m;
    Sep.inames_ok_single i p m;
    IA.intro_read_inv' i p (frame ** Sep.mem_invariant (add_inv mask i) m) m;
    Sep.mem_invariant_equiv mask m i;
    assert (FStar.Preorder.reflexive Sep.is_ghost_action);
    hide (), m
  in hide step