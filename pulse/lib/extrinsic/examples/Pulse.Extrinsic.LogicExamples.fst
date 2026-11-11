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

(** Introductory source-level proofs: load/add, store/read, computed operands,
    and conditional update. Exact pure result facts are kept alongside the
    physical ownership needed by subsequent instructions. Each proof composes
    typed logical rules; assert_norm only checks capture-avoiding syntax
    substitution, not an execution.

    Read sequential_correct and round_trip_correct first, then load_plus and
    increment for context composition, and finally zero_test/set_if_zero.
    increment requires exclusive points-to and is NOT a concurrent increment. *)

open Pulse.Extrinsic.HeapLang
open Pulse.Extrinsic.HeapLang.Notation
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module R = Pulse.Extrinsic.Rules
module S = PulseCore.IndirectionTheorySep

let increment_result : expr [TInt] TInt = add (Var Here) (int_ 1)

let sequential (r:PulseCore.Heap.core_ref) : expr [] TInt =
  let! observed = load (ref_ r) in
  add observed (int_ 1)

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
  store (ref_ r) (int_ desired) >> load (ref_ r)

let round_trip_correct (r:PulseCore.Heap.core_ref) (old desired:int)
  : Lemma (P.hoare (C.points_to r old) (round_trip r desired) (P.read_post r desired))
  = P.store r old desired;
    P.load r desired;
    P.sequence (C.points_to r old) (C.points_to r desired)
      (Store (Val r) (Val desired)) (Load (Val r)) (P.read_post r desired)

let load_plus (r:PulseCore.Heap.core_ref) : expr [] TInt =
  add (load (ref_ r)) (int_ 1)

let load_plus_correct (r:PulseCore.Heap.core_ref) (old:int)
  : Lemma (P.hoare (C.points_to r old) (load_plus r)
      (P.framed_post (P.returns_value (old + 1)) (C.points_to r old)))
  = let p = C.points_to r old in
    let q = P.framed_post (P.returns_value (old + 1)) p in
    let k = AddLeft Hole (Val 1) in
    S.sep_laws ();
    P.load r old;
    introduce forall v. P.hoare (P.read_post r old v) (fill k (Val v)) q with (
      P.pure_pre p (v == old) (Add (Val v) (Val 1)) q (fun _ ->
        P.add v 1;
        P.frame S.emp (Add (Val v) (Val 1)) (P.returns_value (v + 1)) p)
    );
    P.context_rule k p (Load (Val r)) (P.read_post r old) q

let increment (r:PulseCore.Heap.core_ref) : expr [] TUnit =
  store (ref_ r) (load_plus r)

let increment_correct (r:PulseCore.Heap.core_ref) (old:int)
  : Lemma (P.hoare (C.points_to r old) (increment r)
      (P.constant_post (C.points_to r (old + 1))))
  = let p = C.points_to r old in
    let mid = P.framed_post (P.returns_value (old + 1)) p in
    let q = P.constant_post #TUnit (C.points_to r (old + 1)) in
    let k = StoreRight r Hole in
    S.sep_laws ();
    load_plus_correct r old;
    introduce forall v. P.hoare (mid v) (fill k (Val v)) q with (
      P.pure_pre p (v == old + 1) (Store (Val r) (Val v)) q
        (fun _ -> P.store r old v)
    );
    P.context_rule k p (load_plus r) mid q

let zero_test (r:PulseCore.Heap.core_ref) : expr [] TBool =
  eq (int_ 0) (load (ref_ r))

let zero_test_correct (r:PulseCore.Heap.core_ref) (old:int)
  : Lemma (P.hoare (C.points_to r old) (zero_test r)
      (P.framed_post (P.returns_value (0 = old)) (C.points_to r old)))
  = let p = C.points_to r old in
    let q = P.framed_post (P.returns_value (0 = old)) p in
    let k = EqRight 0 Hole in
    S.sep_laws ();
    P.load r old;
    introduce forall v. P.hoare (P.read_post r old v) (fill k (Val v)) q with (
      P.pure_pre p (v == old) (Eq (Val 0) (Val v)) q (fun _ ->
        P.eq 0 v;
        P.frame S.emp (Eq (Val 0) (Val v)) (P.returns_value (0 = v)) p)
    );
    P.context_rule k p (Load (Val r)) (P.read_post r old) q

let set_if_zero (r:PulseCore.Heap.core_ref) : expr [] TUnit =
  if_ (zero_test r) (store (ref_ r) (int_ 1)) unit_

let set_if_zero_correct (r:PulseCore.Heap.core_ref) (old:int)
  : Lemma (P.hoare (C.points_to r old) (set_if_zero r)
      (P.constant_post (C.points_to r (if old = 0 then 1 else old))))
  = let p = C.points_to r old in
    let q = P.constant_post #TUnit (C.points_to r (if old = 0 then 1 else old)) in
    let mid = P.framed_post (P.returns_value (0 = old)) p in
    let yes = Store (Val r) (Val 1) in
    let no : expr [] TUnit = Val () in
    let k = IfCtx Hole yes no in
    S.sep_laws ();
    zero_test_correct r old;
    introduce forall b. P.hoare (mid b) (fill k (Val b)) q with (
      P.pure_pre p (b == (0 = old)) (If (Val b) yes no) q (fun _ ->
        (if b then P.store r old 1 else (R.entails_refl p; P.value_rule p () q));
        P.if_value p b yes no q)
    );
    P.context_rule k p (zero_test r) mid q
