module Pulse.Extrinsic.AtomicIncrementExamples

(** Independent clients of the multi-step AtomicIncrement contract.
    owned_protocol uses a pure equality closing witness to preserve the known
    initial value; program allocates and returns a cell containing initial+1.
    shared_protocol instead opens an invariant with an existential value and
    restores it on either abort or commit. Neither client unfolds the CAS
    loop or reasons about its schedules.

    The second client demonstrates nonempty-mask composition, not an exact
    final shared count: arbitrary interference is allowed between attempts. *)

open Pulse.Extrinsic.HeapLang
open Pulse.Extrinsic.HeapLang.Notation
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module R = Pulse.Extrinsic.Rules
module U = Pulse.Extrinsic.HeapLang.AtomicUpdate
module I = Pulse.Extrinsic.HeapLang.AtomicIncrement
module GS = Pulse.Lib.GhostSet

let owned_closing (initial:int) (observed:int) = S.pure (observed == initial)

(** Exclusive call-entry ownership keeps the observed value equal to initial.
    The closing witness is pure, but using either branch still requires the
    exclusive physical alpha/beta resource. *)
let owned_protocol (r:H.core_ref) (initial:int)
  : Lemma (U.protocol GS.empty GS.empty (C.points_to r initial)
      (I.alpha r) (I.beta r) (I.finished (C.points_to r (initial + 1))) (owned_closing initial))
  = S.sep_laws ();
    let opening = fun old -> S.star (I.alpha r old) (owned_closing initial old) in
    assert_norm (U.opened (I.alpha r) (owned_closing initial) ==
      S.op_exists_Star (fun old -> S.star (I.alpha r old) (owned_closing initial old)));
    R.fact_emp (initial == initial);
    R.exists_intro opening initial;
    P.update_entails GS.empty (C.points_to r initial)
      (U.opened (I.alpha r) (owned_closing initial));
    introduce forall old. P.update GS.empty GS.empty
      (S.star (I.alpha r old) (owned_closing initial old)) (C.points_to r initial)
    with (
      R.pure_elim (C.points_to r old) (C.points_to r initial) (old == initial)
        (fun _ -> R.entails_refl (C.points_to r initial));
      P.update_entails GS.empty (opening old) (C.points_to r initial)
    );
    introduce forall old (v:unit). P.update GS.empty GS.empty
      (S.star (I.beta r old v) (owned_closing initial old)) (I.finished (C.points_to r (initial + 1)) old v)
    with (
      let before = S.star (I.beta r old v) (owned_closing initial old) in
      R.pure_elim (C.points_to r (old + 1)) (C.points_to r (initial + 1)) (old == initial)
        (fun _ -> R.entails_refl (C.points_to r (initial + 1)));
      P.update_entails GS.empty before (C.points_to r (initial + 1))
    )

let body (initial:int) : expr [TRef] TRef =
  let cell = Var Here in
  I.increment_at cell >> cell
let program (initial:int) : expr [] TRef =
  let! cell = alloc (int_ initial) in
  I.increment_at cell >> cell

let program_correct (initial:int)
  : Lemma (P.hoare S.emp (program initial) (P.allocation_post (initial + 1)))
  = P.alloc initial;
    introduce forall r. P.hoare (C.points_to r initial) (substitute r (body initial))
      (P.allocation_post (initial + 1))
    with (
      owned_protocol r initial;
      I.correct r GS.empty (C.points_to r initial) (owned_closing initial) (C.points_to r (initial + 1));
      R.entails_refl (C.points_to r (initial + 1));
      P.value_rule (C.points_to r (initial + 1)) r (P.allocation_post (initial + 1));
      P.sequence (C.points_to r initial) (C.points_to r (initial + 1))
        (I.increment r) (Val r) (P.allocation_post (initial + 1));
      assert_norm (substitute r (body initial) == Seq (I.increment r) (Val r))
    );
    P.let_rule S.emp (Alloc (Val initial)) (body initial)
      (P.allocation_post initial) (P.allocation_post (initial + 1))

let shared_body (r:H.core_ref) = S.op_exists_Star (C.points_to r)
let shared_closing (i:S.iref) (r:H.core_ref) (_:int) = S.inv i (shared_body r)

let shared_close (i:S.iref) (r:H.core_ref) (old:int)
  : Lemma (P.update (S.add_inv GS.empty i) GS.empty
      (S.star (C.points_to r old) (S.inv i (shared_body r))) (S.inv i (shared_body r)))
  = S.sep_laws ();
    let contents = shared_body r in
    let shared = S.inv i contents in
    let mask = S.add_inv GS.empty i in
    R.exists_intro (C.points_to r) old;
    R.entails_exposed contents;
    R.entails_trans (C.points_to r old) contents (P.exposed contents);
    R.entails_refl shared;
    R.entails_star (C.points_to r old) (P.exposed contents) shared shared;
    P.update_entails mask (S.star (C.points_to r old) shared) (S.star shared (P.exposed contents));
    P.close_invariant GS.empty i contents;
    P.update_trans mask mask GS.empty (S.star (C.points_to r old) shared)
      (S.star shared (P.exposed contents)) shared

(** Open to an existential value, frame the handle as closing ownership, and
    close at old for abort or old+1 for commit. Exposure is justified for
    points-to; this does not remove later from arbitrary invariant bodies. *)
let shared_protocol (i:S.iref) (r:H.core_ref)
  : Lemma (
      let shared = S.inv i (shared_body r) in
      U.protocol GS.empty (S.add_inv GS.empty i) shared (I.alpha r) (I.beta r)
        (I.finished shared) (shared_closing i r))
  = S.sep_laws ();
    let contents = shared_body r in
    let shared = S.inv i contents in
    let mask = S.add_inv GS.empty i in
    let opening = U.opened (I.alpha r) (shared_closing i r) in
    P.open_invariant GS.empty i contents;
    introduce forall old. S.implies (P.exposed (C.points_to r old)) (C.points_to r old)
    with C.points_to_exposed r old;
    R.exposed_exists (C.points_to r);
    R.entails_refl shared;
    R.entails_star (P.exposed contents) contents shared shared;
    R.exists_star (C.points_to r) shared;
    S.exists_ext (fun old -> S.star (I.alpha r old) (shared_closing i r old))
      (fun old -> S.star (C.points_to r old) shared);
    assert_norm (U.opened (I.alpha r) (shared_closing i r) ==
      S.op_exists_Star (fun old -> S.star (I.alpha r old) (shared_closing i r old)));
    P.update_entails mask (S.star shared (P.exposed contents)) opening;
    P.update_trans GS.empty mask mask shared (S.star shared (P.exposed contents)) opening;
    introduce forall old. P.update mask GS.empty (S.star (I.alpha r old) (shared_closing i r old)) shared
    with shared_close i r old;
    introduce forall old (v:unit). P.update mask GS.empty
      (S.star (I.beta r old v) (shared_closing i r old)) (I.finished shared old v)
    with shared_close i r (old + 1)

let shared_increment (i:S.iref) (r:H.core_ref)
  : Lemma (P.hoare (S.inv i (shared_body r)) (I.increment r)
      (P.constant_post (S.inv i (shared_body r))))
  = shared_protocol i r;
    I.correct r (S.add_inv GS.empty i) (S.inv i (shared_body r))
      (shared_closing i r) (S.inv i (shared_body r))
