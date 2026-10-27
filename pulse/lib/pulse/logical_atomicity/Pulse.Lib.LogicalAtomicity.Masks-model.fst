module Pulse.Lib.LogicalAtomicity.Masks

friend Pulse.Lib.Core
friend Pulse.Lib.Core.Inv
friend PulseCore.Action
friend PulseCore.InstantiatedSemantics

open FStar.Ghost
open Pulse.Lib.Core
open PulseCore.Observability
module I = Pulse.Lib.Core.Inv
module S = PulseCore.IndirectionTheorySep
module A = PulseCore.Action
module AT = PulseCore.Atomic
module H = PulseCore.HoareStateMonad
module IA = PulseCore.IndirectionTheoryActions

private let somewhere_eq (p:slprop)
  : Lemma (I.somewhere (later p) == S.somewhere (S.later p)) =
  assert (I.somewhere (later p) == S.somewhere (S.later p))
    by (FStar.Tactics.V2.trefl ())

let action (a:Type u#a) (obs:observability)
  (before after:inames) (pre:slprop) (post:a -> slprop)
  : Type u#(max 4 a)
  = frame:slprop ->
    H.st #S.full_mem a
      (fun m ->
        S.budget m >= 0 /\ (obs == Observable ==> S.budget m > 0) /\
        S.inames_ok before m /\
        S.interp (pre ** frame ** S.mem_invariant before m) m)
      (fun m0 x m1 ->
        S.budget m0 - S.budget m1 <= 1 /\
        (obs == Neutral ==> S.is_ghost_action m0 m1 /\ S.budget m0 == S.budget m1) /\
        S.inames_ok after m1 /\
        S.interp (post x ** frame ** S.mem_invariant after m1) m1)

let gaction a before after pre post =
  erased (action (erased a) Neutral before after pre (fun x -> post (reveal x)))

let return #a mask x post : action a Neutral mask mask (post x) post =
  fun frame m ->
    assert (FStar.Preorder.reflexive S.is_ghost_action);
    x, m

let bind #a #b #o1 #o2 #m1 #m2 #m3 #p #q #r f g
  : action b (join_obs o1 o2) m1 m3 p r =
  assert (FStar.Preorder.transitive S.is_ghost_action);
  fun frame m0 ->
    let x, m1 = f frame m0 in
    g x frame m1

let frame #a #o #m1 #m2 #p #q r f
  : action a o m1 m2 (p ** r) (fun x -> q x ** r) =
  S.sep_laws ();
  fun frame -> f (r ** frame)

let lift_atomic #a #o #opens #p #q mask f
  : action a o mask mask p q =
  let (| t, decode, step |) = AT.as_action f #mask in
  fun frame m0 ->
    let x, m1 = step frame m0 in
    decode x, m1

let lift_ghost #a #opens #p #q mask f
  : gaction a mask mask p q =
  hide (lift_atomic mask (AT.lift_ghost_neutral' f))

let ghost_to_action #a #m1 #m2 #p #q f
  : action (erased a) Neutral m1 m2 p (fun x -> q x) =
  fun frame m0 ->
    let result : erased (erased a & S.full_mem) = hide ((reveal f) frame m0) in
    let x : erased a = fst result in
    let m1 = S.update_ghost m0 (hide (snd result)) in
    x, m1

let bind_ghost #a #b #m1 #m2 #m3 #p #q #r f g
  : gaction b m1 m3 p r =
  hide (bind (ghost_to_action f) (fun x -> ghost_to_action (g (reveal x))))

let frame_ghost #a #m1 #m2 #p #q r f
  : gaction a m1 m2 (p ** r) (fun x -> q x ** r) =
  hide (frame r (ghost_to_action f))

let action_to_ghost #a #m1 #m2 #p #q f
  : gaction a m1 m2 p q =
  hide (fun frame m0 ->
    let x, m1 = f frame m0 in
    hide x, m1)

let sub_ghost #a #m1 #m2 #p #q p' q' f
  : gaction a m1 m2 p' q' =
  hide (fun frame m0 -> ghost_to_action f frame m0)

let reindex_ghost #a #m1 #m2 #p #q before after f = f

let finish_ghost #a #m1 #m2 #p x post f =
  bind (ghost_to_action f) (fun _ -> return m2 x post)

let run #a #o #p #q opens f : stt_atomic a #o opens p q =
  AT.of_action (A.lift_pre_act0_act (fun #mask -> f mask))

let run_closed #a #o #p #q f : stt_atomic a #o all_inames p q =
  run all_inames (fun mask ->
    FStar.GhostSet.lemma_equal_intro mask emp_inames;
    f)

let open_invariant mask i p
  : gaction unit mask (add_inv mask i)
      (I.inv i p) (fun _ -> I.inv i p ** I.somewhere (later p)) =
  let step : action (erased unit) Neutral mask (add_inv mask i)
      (I.inv i p) (fun _ -> I.inv i p ** I.somewhere (later p)) =
    fun frame m ->
    S.sep_laws ();
    somewhere_eq p;
    S.destruct_star_l (I.inv i p) (frame ** S.mem_invariant mask m) m;
    S.inames_ok_single i p m;
    S.mem_invariant_equiv mask m i;
    IA.elim_read_inv i p (frame ** S.mem_invariant (add_inv mask i) m) m;
    S.inames_ok_union (single i) mask m;
    assert (FStar.Preorder.reflexive S.is_ghost_action);
    hide (), m
  in hide step

let close_invariant mask i p
  : gaction unit (add_inv mask i) mask
      (I.inv i p ** I.somewhere (later p)) (fun _ -> I.inv i p) =
  let step : action (erased unit) Neutral (add_inv mask i) mask
      (I.inv i p ** I.somewhere (later p)) (fun _ -> I.inv i p) =
    fun frame m ->
    S.sep_laws ();
    somewhere_eq p;
    S.inames_ok_union (single i) mask m;
    S.destruct_star_l (I.inv i p)
      (I.somewhere (later p) ** frame ** S.mem_invariant (add_inv mask i) m) m;
    S.inames_ok_single i p m;
    IA.intro_read_inv' i p (frame ** S.mem_invariant (add_inv mask i) m) m;
    S.mem_invariant_equiv mask m i;
    assert (FStar.Preorder.reflexive S.is_ghost_action);
    hide (), m
  in hide step
