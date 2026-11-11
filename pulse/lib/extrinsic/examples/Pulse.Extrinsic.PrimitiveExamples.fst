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
module Pulse.Extrinsic.PrimitiveExamples

(** Small source clients isolating allocation and CAS/while reasoning.
    new_counter allocates old, performs a non-atomic exclusive increment, and
    returns its reference with ownership of old+1. cas_until_failure runs
    CAS(0,1) until it fails; starting from a bit cell, either branch of the CAS
    leaves value 1, giving an exact exit assertion without a trace argument.
    Larger concurrent examples rely on the same primitive and loop rules. *)

open Pulse.Extrinsic.HeapLang
open Pulse.Extrinsic.HeapLang.Notation
module P = Pulse.Extrinsic.HeapLang.Proof
module L = Pulse.Extrinsic.HeapLang.Loops
module C = Pulse.Extrinsic.HeapLang.Logic
module S = PulseCore.IndirectionTheorySep
module R = Pulse.Extrinsic.Rules
module B = Pulse.Extrinsic.ExamplePredicates
module X = Pulse.Extrinsic.LogicExamples
module GS = Pulse.Lib.GhostSet

let initialize : expr [TRef] TRef =
  let cell = Var Here in
  store cell (add (load cell) (int_ 1)) >> cell

let new_counter (old:int) : expr [] TRef =
  let! cell = alloc (int_ old) in
  store cell (add (load cell) (int_ 1)) >> cell

let new_counter_correct (old:int)
  : Lemma (P.hoare S.emp (new_counter old) (P.allocation_post (old + 1)))
  = let q = P.allocation_post (old + 1) in
    P.alloc old;
    introduce forall r. P.hoare (P.allocation_post old r) (substitute r initialize) q
    with (
      assert_norm (substitute r initialize == Seq (X.increment r) (Val r));
      X.increment_correct r old;
      R.entails_refl (C.points_to r (old + 1));
      P.value_rule (C.points_to r (old + 1)) r q;
      P.sequence (C.points_to r old) (C.points_to r (old + 1))
        (X.increment r) (Val r) q
    );
    P.let_rule S.emp (Alloc (Val old)) initialize (P.allocation_post old) q

let cas_until_failure (r:PulseCore.Heap.core_ref) : expr [] TUnit =
  while_ (cas (ref_ r) (int_ 0) (int_ 1)) unit_

let cas_until_failure_correct (r:PulseCore.Heap.core_ref)
  : Lemma (P.hoare (B.bit_cell r) (cas_until_failure r)
      (P.constant_post (C.points_to r 1)))
  = S.sep_laws ();
    let inv = B.bit_cell r in
    let one = C.points_to r 1 in
    let condition = Cas (Val r) (Val 0) (Val 1) in
    let mid = L.condition_post one one in
    B.bit_cell_unfold r;
    introduce forall (old:B.bit). P.atomic GS.empty (B.bit_point r old) condition mid
    with (
      P.atomic_cas GS.empty r old 0 1;
      R.entails_refl (C.points_to r old);
      introduce forall b. S.implies (P.cas_post r old 0 1 b) (mid b)
      with (
        R.pure_elim (C.points_to r (if b then 1 else old)) (mid b) (b == (old = 0))
          (fun _ -> R.entails_refl one)
      );
      P.atomic_consequence GS.empty (C.points_to r old) (C.points_to r old)
        condition (P.cas_post r old 0 1) mid
    );
    P.atomic_exists GS.empty (B.bit_point r) condition mid;
    P.atomic_to_hoare inv condition mid;
    B.bit_cell_intro r 1;
    P.value_rule one () (P.constant_post inv);
    L.while_rule inv one one condition (Val ())
