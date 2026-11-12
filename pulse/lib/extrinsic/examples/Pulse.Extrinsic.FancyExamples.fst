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
module Pulse.Extrinsic.FancyExamples

(** Clients of assertion-valued updates and the update-closed source WP.
    allocate_at_value performs logical invariant allocation without pretending
    the returned unit takes a source step. composed_value then uses a source
    let rule whose continuation is also a value.
    deferred_allocation packages that same update as owned assertion state.
    None of these proofs constructs a logical memory or a source execution. *)

open Pulse.Extrinsic.HeapLang
open Pulse.Extrinsic.HeapLang.Notation
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module FP = Pulse.Extrinsic.HeapLang.FancyProof
module R = Pulse.Extrinsic.Rules
module GS = Pulse.Lib.GhostSet
module A = Pulse.Extrinsic.HeapLang.Adequacy
module E = Pulse.Extrinsic.HeapLang.Semantics
module Lang = Pulse.Extrinsic.Language

let allocate_at_value (p:S.slprop)
  : Lemma (FP.hoare p (Val ()) (P.constant_post (P.allocated p)))
  = P.update_allocate p;
    FP.value_rule p () (P.constant_post (P.allocated p))

(** Already-returned programs need not manufacture a source step, even when
    their postcondition performs a ghost update and the horizon is positive. *)
let value_runs (h:PulseCore.Heap.full_heap u#3) (n:nat)
  : Lemma (Lang.runs_for E.language n
      { Lang.threads = [E.Pack TUnit (Val ())]; Lang.state = h })
  = allocate_at_value S.emp;
    A.emp_realizable h;
    A.can_run_fancy S.emp (Val ()) (P.constant_post (P.allocated S.emp)) h n

let deferred_allocation (p:S.slprop)
  : Lemma (S.implies p (FP.fupd GS.empty GS.empty (P.allocated p)))
  = P.update_allocate p;
    FP.update_intro GS.empty GS.empty p (P.allocated p)

let composed : expr [] TUnit =
  let! result = unit_ in
  result

let composed_value (p:S.slprop)
  : Lemma (FP.hoare p composed (P.constant_post (P.allocated p)))
  = allocate_at_value p;
    introduce forall (v:unit). FP.hoare (P.allocated p) (substitute v (Var Here))
      (P.constant_post (P.allocated p))
    with (
      R.entails_refl (P.allocated p);
      P.update_entails GS.empty (P.allocated p) (P.allocated p);
      FP.value_rule (P.allocated p) v (P.constant_post (P.allocated p));
      assert_norm (substitute #[] v (Var Here) == Val v)
    );
    FP.let_rule p (Val ()) (Var Here) (P.constant_post (P.allocated p))
      (P.constant_post (P.allocated p))

let framed_value (p frame:S.slprop)
  : Lemma (FP.hoare (S.star p frame) (Val ())
      (P.constant_post (S.star (P.allocated p) frame)))
  = allocate_at_value p;
    FP.frame p (Val ()) (P.constant_post (P.allocated p)) frame;
    let pre = S.star p frame in
    let q = P.framed_post (P.constant_post #TUnit (P.allocated p)) frame in
    let post = P.constant_post #TUnit (S.star (P.allocated p) frame) in
    R.entails_refl pre;
    introduce forall v. S.implies (q v) (post v) with R.entails_refl (post v);
    FP.consequence pre pre (Val ()) q post

let post_allocation (p:S.slprop)
  : Lemma (FP.hoare p (Val ()) (P.constant_post (P.allocated p)))
  = R.entails_refl p;
    P.value_rule p () (P.constant_post p);
    FP.embed p (Val ()) (P.constant_post p);
    introduce forall (v:unit). P.update GS.empty GS.empty p (P.allocated p)
    with P.update_allocate p;
    FP.post_update p (Val ()) (P.constant_post p) (P.constant_post (P.allocated p))
