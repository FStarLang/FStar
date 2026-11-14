module Pulse.Extrinsic.HeapLang.AtomicIncrement

(** Prove the loop against the logical protocol, without inspecting its
    representation. read opens and aborts, retaining no stable value fact.
    compare_exchange opens again at the actual CAS step and either aborts with
    unchanged alpha or commits beta. attempt composes arithmetic and boolean
    control; correct applies the general while rule with retry as invariant.
    Masks are closed between source steps, including failed attempts. *)

open Pulse.Extrinsic.HeapLang
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module U = Pulse.Extrinsic.HeapLang.AtomicUpdate
module R = Pulse.Extrinsic.Rules
module L = Pulse.Extrinsic.HeapLang.Loops
module GS = Pulse.Lib.GhostSet

let opened r closing = U.opened (alpha r) closing
let piece (r:H.core_ref) (closing:int -> S.slprop) (old:int) =
  S.star (C.points_to r old) (closing old)

(** This read is speculative: another thread may change the cell before CAS.
    Abort the opening and return retry for every read result, deliberately
    forgetting the observed value's relation to the current abstract state. *)
let read (r:H.core_ref) (inner:S.inames) (retry:S.slprop)
  (closing:int -> S.slprop) (result:S.slprop)
  : Lemma
      (requires U.protocol GS.empty inner retry (alpha r) (beta r) (finished result) closing)
      (ensures P.hoare retry (Load (Val r)) (P.constant_post retry))
  = S.sep_laws ();
    let e = Load (Val r) in
    let post = P.constant_post #TInt (opened r closing) in
    assert_norm (opened r closing == S.op_exists_Star (piece r closing));
    introduce forall old. P.atomic inner (piece r closing old) e post
    with (
      let raw = P.framed_post (P.read_post r old) (closing old) in
      P.atomic_load inner r old;
      P.atomic_frame inner (C.points_to r old) e (P.read_post r old) (closing old);
      R.entails_refl (piece r closing old);
      introduce forall v. S.implies (raw v) (post v)
      with (
        R.entails_left (piece r closing old) (S.pure (v == old));
        R.exists_intro (piece r closing) old;
        R.entails_trans (raw v) (piece r closing old) (post v)
      );
      P.atomic_consequence inner (piece r closing old) (piece r closing old) e raw post
    );
    P.atomic_exists inner (piece r closing) e post;
    introduce forall old. P.update inner GS.empty (piece r closing old) retry with ();
    P.update_exists inner GS.empty (piece r closing) retry;
    P.atomic_updates GS.empty inner retry (opened r closing) e post (P.constant_post retry);
    P.atomic_to_hoare retry e (P.constant_post retry)

let outcome (retry result:S.slprop) (success:bool) = if success then result else retry
let cas_piece (r:H.core_ref) (closing:int -> S.slprop) (expected:int) (success:bool) (old:int) =
  S.star (P.cas_post r old expected (expected + 1) success) (closing old)
let cas_post r closing expected success = S.op_exists_Star (cas_piece r closing expected success)

(** The linearizing step. The fresh opening exposes actual old, not the
    earlier expected value. CAS equality makes beta available only on success;
    on failure alpha and the same closing capability restore retry. *)
let compare_exchange (r:H.core_ref) (inner:S.inames) (retry:S.slprop)
  (closing:int -> S.slprop) (result:S.slprop) (expected:int)
  : Lemma
      (requires U.protocol GS.empty inner retry (alpha r) (beta r) (finished result) closing)
      (ensures P.hoare retry (Cas (Val r) (Val expected) (Val (expected + 1))) (outcome retry result))
  = S.sep_laws ();
    let e = Cas (Val r) (Val expected) (Val (expected + 1)) in
    let post = cas_post r closing expected in
    assert_norm (opened r closing == S.op_exists_Star (piece r closing));
    introduce forall old. P.atomic inner (piece r closing old) e post
    with (
      let raw = P.framed_post (P.cas_post r old expected (expected + 1)) (closing old) in
      P.atomic_cas inner r old expected (expected + 1);
      P.atomic_frame inner (C.points_to r old) e (P.cas_post r old expected (expected + 1)) (closing old);
      R.entails_refl (piece r closing old);
      introduce forall b. S.implies (raw b) (post b)
      with R.exists_intro (cas_piece r closing expected b) old;
      P.atomic_consequence inner (piece r closing old) (piece r closing old) e raw post
    );
    P.atomic_exists inner (piece r closing) e post;
    introduce forall b. P.update inner GS.empty (post b) (outcome retry result b)
    with (
      introduce forall old. P.update inner GS.empty (cas_piece r closing expected b old)
        (outcome retry result b)
      with (
        let plain = S.star (C.points_to r (if b then expected + 1 else old)) (closing old) in
        P.update_pure_pre inner GS.empty plain (outcome retry result b) (b == (old = expected))
          (fun _ ->
            if b then (
              eliminate forall x y. P.update inner GS.empty
                (S.star (beta r x y) (closing x)) (finished result x y)
              with old ()
            ) else (
              eliminate forall x. P.update inner GS.empty
                (S.star (alpha r x) (closing x)) retry
              with old
            ))
      );
      P.update_exists inner GS.empty (cas_piece r closing expected b) (outcome retry result b)
    );
    P.atomic_updates GS.empty inner retry (opened r closing) e post (outcome retry result);
    P.atomic_to_hoare retry e (outcome retry result)

let attempt (r:H.core_ref) (inner:S.inames) (retry:S.slprop)
  (closing:int -> S.slprop) (result:S.slprop) (expected:int)
  : Lemma
      (requires U.protocol GS.empty inner retry (alpha r) (beta r) (finished result) closing)
      (ensures P.hoare retry (substitute expected (retry_at (Val #[] r)))
        (L.condition_post retry result))
  = S.sep_laws ();
    let desired = Add (Val expected) (Val 1) in
    let mid = P.framed_post (P.returns_value (expected + 1)) retry in
    let selected = outcome retry result in
    let post = L.condition_post retry result in
    let k = CasDesired r expected Hole in
    P.add expected 1;
    P.frame S.emp desired (P.returns_value (expected + 1)) retry;
    introduce forall v. P.hoare (mid v) (fill k (Val v)) selected
    with P.pure_pre retry (v == expected + 1) (fill k (Val v)) selected
      (fun _ -> compare_exchange r inner retry closing result expected);
    P.context_rule k retry desired mid selected;
    introduce forall b. P.hoare (selected b) (If (Val b) (Val false) (Val true)) post
    with (
      R.entails_refl (selected b);
      P.value_rule (selected b) (not b) post;
      P.if_value (selected b) b (Val false) (Val true) post
    );
    P.context_rule (IfCtx Hole (Val false) (Val true)) retry (fill k desired) selected post;
    assert_norm (substitute expected (retry_at (Val #[] r)) ==
      If (fill k desired) (Val false) (Val true))

let correct r inner retry closing result =
  read r inner retry closing result;
  introduce forall old. P.hoare retry (substitute old (retry_at (Val #[] r)))
    (L.condition_post retry result)
  with attempt r inner retry closing result old;
  P.let_rule retry (Load (Val r)) (retry_at (Val #[] r)) (P.constant_post retry)
    (L.condition_post retry result);
  R.entails_refl retry;
  P.value_rule retry () (P.constant_post retry);
  L.while_rule retry retry result (Let (Load (Val r)) (retry_at (Val #[] r))) (Val ())
