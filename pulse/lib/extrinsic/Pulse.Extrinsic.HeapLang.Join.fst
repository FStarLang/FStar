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

open Pulse.Extrinsic.HeapLang
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module R = Pulse.Extrinsic.Rules
module L = Pulse.Extrinsic.HeapLang.Loops
module GS = Pulse.Lib.GhostSet

let stored (payload:S.slprop) (n:phase) = if n = 1 then payload else S.emp
let piece (flag:H.core_ref) (payload:S.slprop) (n:phase) =
  S.star (C.points_to flag n) (stored payload n)
let body flag payload = S.op_exists_Star (piece flag payload)

let initialize flag payload =
  S.sep_laws ();
  R.exists_intro (piece flag payload) 0

let initialize_ready flag payload =
  R.exists_intro (piece flag payload) 1

let expose (flag:H.core_ref) (payload:S.slprop)
  : Lemma
      (requires S.implies (P.exposed payload) payload)
      (ensures S.implies (P.exposed (body flag payload)) (body flag payload))
  = introduce forall (n:phase). S.implies (P.exposed (piece flag payload n)) (piece flag payload n)
    with (
      C.points_to_exposed flag n;
      if n <> 1 then R.entails_emp (P.exposed S.emp);
      R.exposed_star (C.points_to flag n) (stored payload n)
    );
    R.exposed_exists (piece flag payload)

let signal_correct i flag payload =
  S.sep_laws ();
  let mask = S.add_inv GS.empty i in
  let contents = body flag payload in
  let shared = handle i flag payload in
  let e = signal flag in
  let post = P.prepend_post (P.exposed contents) (P.constant_post #TUnit S.emp) in
  introduce forall (n:phase). P.atomic mask (S.star (piece flag payload n) payload) e post
  with (
    let tail = S.star (stored payload n) payload in
    let raw = P.framed_post (P.constant_post #TUnit (C.points_to flag 1)) tail in
    P.atomic_store mask flag n 1;
    P.atomic_frame mask (C.points_to flag n) e (P.constant_post (C.points_to flag 1)) tail;
    R.entails_refl (S.star (piece flag payload n) payload);
    introduce forall v. S.implies (raw v) (post v)
    with (
      R.entails_left (piece flag payload 1) (stored payload n);
      R.exists_intro (piece flag payload) 1;
      R.entails_trans (raw v) (piece flag payload 1) contents;
      R.entails_exposed contents;
      R.entails_trans (raw v) contents (post v)
    );
    P.atomic_consequence mask (S.star (piece flag payload n) payload)
      (S.star (piece flag payload n) payload) e raw post
  );
  P.atomic_exists mask (fun (n:phase) -> S.star (piece flag payload n) payload) e post;
  R.exists_star (piece flag payload) payload;
  expose flag payload;
  R.entails_refl payload;
  R.entails_star (P.exposed contents) contents payload payload;
  introduce forall v. S.implies (post v) (post v) with R.entails_refl (post v);
  P.atomic_consequence mask (S.star contents payload) (S.star (P.exposed contents) payload) e post post;
  P.atomic_invariant GS.empty i contents payload e (P.constant_post #TUnit S.emp);
  R.entails_refl (S.star shared payload);
  introduce forall v. S.implies
    (P.prepend_post shared (P.constant_post #TUnit S.emp) v) (P.constant_post shared v)
  with R.entails_refl shared;
  P.atomic_consequence GS.empty (S.star shared payload) (S.star shared payload) e
    (P.prepend_post shared (P.constant_post S.emp)) (P.constant_post shared);
  P.atomic_to_hoare (S.star shared payload) e (P.constant_post shared)

let returned (payload:S.slprop) (b:bool) = if b then payload else S.emp

let claim (i:S.iref) (flag:H.core_ref) (payload:S.slprop)
  : Lemma
      (requires S.implies (P.exposed payload) payload)
      (ensures P.hoare (handle i flag payload) (Cas (Val flag) (Val 1) (Val 2))
        (P.prepend_post (handle i flag payload) (returned payload)))
  = S.sep_laws ();
    let mask = S.add_inv GS.empty i in
    let contents = body flag payload in
    let shared = handle i flag payload in
    let e = Cas (Val flag) (Val 1) (Val 2) in
    let post = P.prepend_post (P.exposed contents) (returned payload) in
    introduce forall (n:phase). P.atomic mask (piece flag payload n) e post
    with (
      let raw = P.framed_post (P.cas_post flag n 1 2) (stored payload n) in
      P.atomic_cas mask flag n 1 2;
      P.atomic_frame mask (C.points_to flag n) e (P.cas_post flag n 1 2) (stored payload n);
      R.entails_refl (piece flag payload n);
      introduce forall b. S.implies (raw b) (post b)
      with (
        let next : phase = if b then 2 else n in
        let plain = S.star (C.points_to flag next) (stored payload n) in
        R.pure_elim plain (post b) (b == (n = 1)) (fun _ ->
          R.exists_intro (piece flag payload) next;
          R.entails_refl (returned payload b);
          R.entails_star (piece flag payload next) contents (returned payload b) (returned payload b);
          R.entails_exposed contents;
          R.entails_star contents (P.exposed contents) (returned payload b) (returned payload b);
          R.entails_trans plain (S.star contents (returned payload b)) (post b)
        )
      );
      P.atomic_consequence mask (piece flag payload n) (piece flag payload n) e raw post
    );
    P.atomic_exists mask (piece flag payload) e post;
    expose flag payload;
    introduce forall v. S.implies (post v) (post v) with R.entails_refl (post v);
    P.atomic_consequence mask contents (P.exposed contents) e post post;
    P.atomic_invariant GS.empty i contents S.emp e (returned payload);
    P.atomic_to_hoare shared e (P.prepend_post shared (returned payload))

let wait_correct i flag payload =
  S.sep_laws ();
  let shared = handle i flag payload in
  let result = P.prepend_post shared (returned payload) in
  let post = L.condition_post shared (S.star shared payload) in
  let e = Cas (Val flag) (Val 1) (Val 2) in
  claim i flag payload;
  introduce forall b. P.hoare (result b) (If (Val b) (Val false) (Val true)) post
  with (
    R.entails_refl (result b);
    P.value_rule (result b) (not b) post;
    P.if_value (result b) b (Val false) (Val true) post
  );
  P.context_rule (IfCtx Hole (Val false) (Val true)) shared e result post;
  R.entails_refl shared;
  P.value_rule shared () (P.constant_post shared);
  L.while_rule shared shared (S.star shared payload)
    (If e (Val false) (Val true)) (Val ())
