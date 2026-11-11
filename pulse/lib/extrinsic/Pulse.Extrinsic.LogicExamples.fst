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
module Pulse.Extrinsic.LogicExamples

open Pulse.Extrinsic.HeapLang
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module R = Pulse.Extrinsic.Rules
module S = PulseCore.IndirectionTheorySep

let increment_result : expr [TInt] TInt = Add (Var Here) (Val 1)

let sequential (r:PulseCore.Heap.core_ref) : expr [] TInt =
  Let (Load (Val r)) increment_result

let sequential_correct (r:PulseCore.Heap.core_ref) (old:int)
  : Lemma (P.hoare (C.points_to r old) (sequential r)
      (P.framed_post (P.returns_value (old + 1)) (C.points_to r old)))
  = let p = C.points_to r old in
    let q = P.framed_post (P.returns_value (old + 1)) p in
    S.sep_laws ();
    P.load r old;
    introduce forall v. P.hoare (P.read_post r old v) (substitute v increment_result) q
    with (
      assert_norm (substitute v increment_result == Add (Val v) (Val 1));
      P.pure_pre p (v == old) (Add (Val v) (Val 1)) q (fun _ ->
        P.add v 1;
        P.frame S.emp (Add (Val v) (Val 1)) (P.returns_value (v + 1)) p)
    );
    P.let_rule p (Load (Val r)) increment_result (P.read_post r old) q

let round_trip (r:PulseCore.Heap.core_ref) (desired:int) : expr [] TInt =
  Seq (Store (Val r) (Val desired)) (Load (Val r))

let round_trip_correct (r:PulseCore.Heap.core_ref) (old desired:int)
  : Lemma (P.hoare (C.points_to r old) (round_trip r desired) (P.read_post r desired))
  = P.store r old desired;
    P.load r desired;
    P.sequence (C.points_to r old) (C.points_to r desired)
      (Store (Val r) (Val desired)) (Load (Val r)) (P.read_post r desired)
