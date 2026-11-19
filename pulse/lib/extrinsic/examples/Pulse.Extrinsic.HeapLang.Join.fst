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
module Pulse.Extrinsic.HeapLang.Join

(** Proof of the completion program using only the source logic.
    The invariant owns flag |-> phase and owns payload only in phase 1.
    signal moves to phase 1 with the supplied payload. claim opens around
    one CAS: success changes 1 to 2 and releases payload; failure preserves
    the invariant. wait_correct feeds this resource-sensitive boolean result
    into the general while rule. No scheduler trace is used. *)

open Pulse.Extrinsic.HeapLang
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module R = Pulse.Extrinsic.Rules
module L = Pulse.Extrinsic.HeapLang.Loops
module GS = Pulse.Lib.GhostSet
module I = Pulse.Extrinsic.HeapLang.Invariants

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

let stored (payload:S.slprop) (n:phase) = if n = 1 then payload else S.emp
let piece (flag:H.core_ref) (payload:S.slprop) (n:phase) =
  S.star (C.points_to flag n) (stored payload n)
let body flag payload = S.op_exists_Star (piece flag payload)

let initialize flag payload =
  S.sep_laws ();
  R.exists_intro (piece flag payload) 0

let initialize_ready flag payload =
  R.exists_intro (piece flag payload) 1

let guarded_piece (flag:H.core_ref) (payload:S.slprop) (n:phase) =
  S.star (C.points_to flag n) (S.later (stored payload n))

(** Only physical points-to is timeless. Keep the payload guarded, even when
    it is itself a higher-order assertion. The source CAS will pay that guard. *)
let expose (flag:H.core_ref) (payload:S.slprop)
  : Lemma (S.implies (S.later (body flag payload)) (S.op_exists_Star (guarded_piece flag payload)))
  = S.later_exists (piece flag payload);
    assert_norm (body flag payload == S.op_exists_Star (fun n -> piece flag payload n));
    introduce forall (n:phase). S.implies (S.later (piece flag payload n))
      (S.op_exists_Star (guarded_piece flag payload))
    with (
      S.later_star (C.points_to flag n) (stored payload n);
      C.points_to_exposed flag n;
      R.entails_refl (S.later (stored payload n));
      R.entails_star (S.later (C.points_to flag n)) (C.points_to flag n)
        (S.later (stored payload n)) (S.later (stored payload n));
      R.exists_intro (guarded_piece flag payload) n;
      R.entails_trans (S.later (piece flag payload n)) (guarded_piece flag payload n)
        (S.op_exists_Star (guarded_piece flag payload))
    );
    R.exists_elim (fun n -> S.later (piece flag payload n)) (S.op_exists_Star (guarded_piece flag payload));
    R.entails_trans (S.later (body flag payload))
      (S.op_exists_Star (fun n -> S.later (piece flag payload n)))
      (S.op_exists_Star (guarded_piece flag payload))

let signal_correct i flag payload =
  S.sep_laws ();
  let mask = S.add_inv GS.empty i in
  let contents = body flag payload in
  let shared = handle i flag payload in
  let e = signal flag in
  let guarded = S.op_exists_Star (guarded_piece flag payload) in
  let post = P.prepend_post (S.later contents) (P.constant_post #TUnit S.emp) in
  introduce forall (n:phase). P.atomic mask (S.star (guarded_piece flag payload n) payload) e post
  with (
    let tail = S.star (S.later (stored payload n)) payload in
    let raw = P.framed_post (P.constant_post #TUnit (C.points_to flag 1)) tail in
    P.atomic_store mask flag n 1;
    P.atomic_frame mask (C.points_to flag n) e (P.constant_post (C.points_to flag 1)) tail;
    R.entails_refl (S.star (guarded_piece flag payload n) payload);
    introduce forall v. S.implies (raw v) (post v)
    with (
      R.entails_left (piece flag payload 1) (S.later (stored payload n));
      R.exists_intro (piece flag payload) 1;
      R.entails_trans (raw v) (piece flag payload 1) contents;
      R.entails_later contents;
      R.entails_trans (raw v) contents (post v)
    );
    P.atomic_consequence mask (S.star (guarded_piece flag payload n) payload)
      (S.star (guarded_piece flag payload n) payload) e raw post
  );
  P.atomic_exists mask (fun (n:phase) -> S.star (guarded_piece flag payload n) payload) e post;
  R.exists_star (guarded_piece flag payload) payload;
  expose flag payload;
  R.entails_refl payload;
  R.entails_star (S.later contents) guarded payload payload;
  introduce forall v. S.implies (post v) (post v) with R.entails_refl (post v);
  P.atomic_consequence mask (S.star guarded payload) (S.star (S.later contents) payload) e post post;
  I.atomic GS.empty i contents payload e (P.constant_post #TUnit S.emp);
  R.entails_refl (S.star shared payload);
  introduce forall v. S.implies
    (P.prepend_post shared (P.constant_post #TUnit S.emp) v) (P.constant_post shared v)
  with R.entails_refl shared;
  P.atomic_consequence GS.empty (S.star shared payload) (S.star shared payload) e
    (P.prepend_post shared (P.constant_post S.emp)) (P.constant_post shared);
  P.atomic_to_hoare (S.star shared payload) e (P.constant_post shared)

let returned (payload:S.slprop) (b:bool) = if b then payload else S.emp

(** The CAS's pure result identifies the old phase. The success branch moves
    stored ownership to returned ownership; it must not duplicate it. *)
let claim (i:S.iref) (flag:H.core_ref) (payload:S.slprop)
  : Lemma
      (ensures P.hoare (handle i flag payload) (Cas (Val flag) (Val 1) (Val 2))
        (P.prepend_post (handle i flag payload) (returned payload)))
  = S.sep_laws ();
    assert_norm (body flag payload == S.op_exists_Star (fun n -> piece flag payload n));
    let mask = S.add_inv GS.empty i in
    let contents = body flag payload in
    let shared = handle i flag payload in
    let e = Cas (Val flag) (Val 1) (Val 2) in
    let guarded = S.op_exists_Star (guarded_piece flag payload) in
    let post = P.prepend_post (S.later contents) (P.later_post (returned payload)) in
    introduce forall (n:phase). P.atomic mask (guarded_piece flag payload n) e post
    with (
      let raw = P.framed_post (P.cas_post flag n 1 2) (S.later (stored payload n)) in
      P.atomic_cas mask flag n 1 2;
      P.atomic_frame mask (C.points_to flag n) e (P.cas_post flag n 1 2) (S.later (stored payload n));
      R.entails_refl (guarded_piece flag payload n);
      introduce forall b. S.implies (raw b) (post b)
      with (
        let next : phase = if b then 2 else n in
        let plain = S.star (C.points_to flag next) (S.later (stored payload n)) in
        R.pure_elim plain (post b) (b == (n = 1)) (fun _ ->
          R.entails_later (C.points_to flag next);
          R.entails_refl (S.later (stored payload n));
          R.entails_star (C.points_to flag next) (S.later (C.points_to flag next))
            (S.later (stored payload n)) (S.later (stored payload n));
          S.later_star (C.points_to flag next) (stored payload n);
          S.later_star (piece flag payload next) (returned payload b);
          S.later_exists (piece flag payload);
          R.exists_intro (fun n -> S.later (piece flag payload n)) next;
          R.entails_refl (S.later contents);
          R.entails_trans (S.later (piece flag payload next))
            (S.op_exists_Star (fun n -> S.later (piece flag payload n))) (S.later contents);
          R.entails_refl (S.later (returned payload b));
          R.entails_star (S.later (piece flag payload next)) (S.later contents)
            (S.later (returned payload b)) (S.later (returned payload b));
          R.entails_trans plain
            (S.star (S.later (piece flag payload next)) (S.later (returned payload b))) (post b)
        )
      );
      P.atomic_consequence mask (guarded_piece flag payload n) (guarded_piece flag payload n) e raw post
    );
    P.atomic_exists mask (guarded_piece flag payload) e post;
    expose flag payload;
    introduce forall v. S.implies (post v) (post v) with R.entails_refl (post v);
    P.atomic_consequence mask guarded (S.later contents) e post post;
    I.atomic GS.empty i contents S.emp e (P.later_post (returned payload));
    let raw = P.prepend_post shared (P.later_post (returned payload)) in
    let q = P.prepend_post shared (returned payload) in
    R.entails_refl shared;
    introduce forall b. S.implies (raw b) (P.later_post q b) with (
      R.entails_later shared;
      R.entails_refl (S.later (returned payload b));
      R.entails_star shared (S.later shared)
        (S.later (returned payload b)) (S.later (returned payload b));
      S.later_star shared (returned payload b)
    );
    P.atomic_consequence GS.empty shared shared e raw (P.later_post q);
    P.atomic_to_hoare_later shared e q

let wait_correct i flag payload =
  S.sep_laws ();
  let shared = handle i flag payload in
  let result = P.prepend_post shared (returned payload) in
  let post = L.condition_post shared (S.star shared payload) in
  let e = Cas (Val flag) (Val 1) (Val 2) in
  claim i flag payload;
  introduce forall b. P.hoare (result b) (fill (IfCtx Hole (Val false) (Val true)) (Val b)) post
  with (
    R.entails_refl (result b);
    P.value_rule (result b) (not b) post;
    P.if_value (result b) b (Val false) (Val true) post;
    assert_norm (fill (IfCtx Hole (Val false) (Val true)) (Val b) ==
      If (Val b) (Val false) (Val true))
  );
  P.context_rule (IfCtx Hole (Val false) (Val true)) shared e result post;
  assert_norm (fill (IfCtx Hole (Val false) (Val true)) e == If e (Val false) (Val true));
  R.entails_refl shared;
  P.value_rule shared () (P.constant_post shared);
  L.while_rule shared shared (S.star shared payload)
    (If e (Val false) (Val true)) (Val ())
