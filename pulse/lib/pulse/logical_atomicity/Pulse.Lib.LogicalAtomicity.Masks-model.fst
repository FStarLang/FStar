module Pulse.Lib.LogicalAtomicity.Masks

(**
Verified model of the paired-mask API in Masks.fsti.

The ambient `mem_invariant mask m` owns invariant bodies except those named
by the open mask. Opening/closing redistributes this assertion; it does not
allocate a new lock or change the physical heap. Each action quantifies over
an arbitrary spatial frame, preserves memory validity, and spends at most
one unit of semantic budget. Neutral actions preserve the budget and satisfy
Pulse's ghost-state transition relation.

These are Pulse model proofs, not new axioms implementing Iris fancy updates.
Friend access is used only to expose existing semantic representations.
The interface's extraction annotations, rather than this model, determine
runtime code; in particular, ghost results cannot affect runtime values.
*)

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

(** Identify the public core invariant wrapper with the semantic localized
assertion. Reflexivity suffices; no locality-erasure principle is assumed. *)
private let somewhere_eq (p:slprop)
  : Lemma (I.somewhere (later p) == S.somewhere (S.later p)) =
  assert (I.somewhere (later p) == S.somewhere (S.later p))
    by (FStar.Tactics.V2.trefl ())

(** A framed Hoare-state transformer with distinct initial/final invariant
resources. Positive budget for observable actions justifies the single step;
the neutral case additionally preserves the concrete state. *)
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

(** Erase both the action witness and its result while retaining its spatial
contract. `ghost_to_action` mediates any use from executable action code. *)
let gaction a before after pre post =
  erased (action (erased a) Neutral before after pre (fun x -> post (reveal x)))

(** Reflexivity of ghost transitions validates an unchanged memory/result. *)
let return #a mask x post : action a Neutral mask mask (post x) post =
  fun frame m ->
    assert (FStar.Preorder.reflexive S.is_ghost_action);
    x, m

(** Compose state transformers. The interface's at-most-one-observable
constraint ensures the combined budget loss is still at most one. *)
let bind #a #b #o1 #o2 #m1 #m2 #m3 #p #q #r f g
  : action b (join_obs o1 o2) m1 m3 p r =
  assert (FStar.Preorder.transitive S.is_ghost_action);
  fun frame m0 ->
    let x, m1 = f frame m0 in
    g x frame m1

(** Absorb the caller's resource into the universally quantified frame. *)
let frame #a #o #m1 #m2 #p #q r f
  : action a o m1 m2 (p ** r) (fun x -> q x ** r) =
  S.sep_laws ();
  fun frame -> f (r ** frame)

(** Decode the existing core action representation at the chosen ambient
mask; its original footprint and observability obligations remain intact. *)
let lift_atomic #a #o #opens #p #q mask f
  : action a o mask mask p q =
  let (| t, decode, step |) = AT.as_action f #mask in
  fun frame m0 ->
    let x, m1 = step frame m0 in
    decode x, m1

(** Use the established ghost-to-neutral embedding, then erase the witness. *)
let lift_ghost #a #opens #p #q mask f
  : gaction a mask mask p q =
  hide (lift_atomic mask (AT.lift_ghost_neutral' f))

(** Replay only a valid ghost-state update through `update_ghost`. This is
the erasure boundary: neither the ghost result nor concrete heap changes
can be manufactured by revealing an erased witness. *)
let ghost_to_action #a #m1 #m2 #p #q f
  : action (erased a) Neutral m1 m2 p (fun x -> q x) =
  fun frame m0 ->
    let result : erased (erased a & S.full_mem) = hide ((reveal f) frame m0) in
    let x : erased a = fst result in
    let m1 = S.update_ghost m0 (hide (snd result)) in
    x, m1

(** Derive erased composition from neutral action composition. *)
let bind_ghost #a #b #m1 #m2 #m3 #p #q #r f g
  : gaction b m1 m3 p r =
  hide (bind (ghost_to_action f) (fun x -> ghost_to_action (g (reveal x))))

(** Derive erased framing without duplicating the framed resource. *)
let frame_ghost #a #m1 #m2 #p #q r f
  : gaction a m1 m2 (p ** r) (fun x -> q x ** r) =
  hide (frame r (ghost_to_action f))

(** Hide the result of an already-neutral transformer; observability rules
out applying this conversion to an arbitrary physical action. *)
let action_to_ghost #a #m1 #m2 #p #q f
  : gaction a m1 m2 p q =
  hide (fun frame m0 ->
    let x, m1 = f frame m0 in
    hide x, m1)

(** Equality of assertions transports the contract without changing memory. *)
let sub_ghost #a #m1 #m2 #p #q p' q' f
  : gaction a m1 m2 p' q' =
  hide (fun frame m0 -> ghost_to_action f frame m0)

(** Equal sets give equal ambient invariant assertions. No resources move. *)
let reindex_ghost #a #m1 #m2 #p #q before after f = f

let localize #a #before #after #pre #post l
  (f:gaction a before after pre post)
  : gaction a before after (on l pre) (fun x -> on l (post x)) =
  let step : action (erased a) Neutral before after (on l pre)
      (fun x -> on l (post (reveal x))) =
    fun frame m0 ->
    S.sep_laws ();
    let l0 = S.current_loc m0 in
    let m1 = S.set_loc m0 l in
    A.impersonate_lem1 l m0 pre before frame;
    let x, m2 = ghost_to_action f (S.loc l ** S.on l0 frame) m1 in
    let m3 = S.set_loc m2 l0 in
    A.impersonate_lem2 l l0 m2 (post (reveal x)) after frame;
    assert (FStar.Preorder.transitive S.is_ghost_action);
    x, m3
  in hide step

(** Sequence erased cleanup before returning the independently supplied `x`. *)
let finish_ghost #a #m1 #m2 #p x post f =
  bind (ghost_to_action f) (fun _ -> return m2 x post)

(** Package a mask-parametric, balanced transformer as an existing Pulse
atomic action. This is why an open invariant cannot escape the combinators. *)
let run #a #o #p #q opens f : stt_atomic a #o opens p q =
  AT.of_action (A.lift_pre_act0_act (fun #mask -> f mask))

(** A mask disjoint from all names must be empty, discharging run's universal
ambient-mask obligation at the cost of the maximal footprint. *)
let run_closed #a #o #p #q f : stt_atomic a #o all_inames p q =
  run all_inames (fun mask ->
    FStar.GhostSet.lemma_equal_intro mask emp_inames;
    f)

(** Split `read_inv i` out of the ambient invariant resource and convert it
to `somewhere (later p)`. The memory is unchanged; only ownership is exposed. *)
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

(** Reverse opening by restoring `read_inv i` to the ambient resource.
Retaining both locality and later is necessary for the existing model proof. *)
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
