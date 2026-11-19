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
module Pulse.Extrinsic.Examples

(** OPERATIONAL REGRESSIONS ONLY, not the method for proving client programs.
    Construct selected executions to exercise allocation, substitution, fork,
    and competing CAS results in the independent semantics. These witnesses
    do not establish correctness for all schedules.
    All separation-logic examples live alongside this file and instead end in
    source Hoare triples, with soundness supplied once by core adequacy. *)

open Pulse.Extrinsic.HeapLang
open Pulse.Extrinsic.HeapLang.Notation
open Pulse.Extrinsic.HeapLang.Semantics
module H = PulseCore.Heap
module M = Pulse.Extrinsic.HeapLang.Memory
module L = Pulse.Extrinsic.Language

let round_trip_body : expr [TRef] TInt =
  Seq (Store (Var Here) (Val 7)) (Load (Var Here))

let round_trip : expr [] TInt =
  Let (Alloc (Val 0)) round_trip_body

let round_trip_runs (h:H.full_heap u#3)
  : h':H.full_heap u#3 & L.execution language 5
      { L.threads = [Pack TInt round_trip]; L.state = h }
      { L.threads = [Pack TInt (Val 7)]; L.state = h' }
  = let (| r, h1 |) = M.allocate 0 h in
    let h2 = M.write r 0 7 h1 in
    M.points_to_contents r 7 h2;
    let s0 = schedule [] [] (ContextStep (LetCtx Hole round_trip_body) (New 0 r h h1 ())) in
    let s1 = schedule [] [] (ContextStep Hole (Beta r round_trip_body h1)) in
    let s2 = schedule [] [] (ContextStep (SeqCtx Hole (Load (Val r))) (Write r 7 h1 h2 ())) in
    let s3 = schedule [] [] (ContextStep Hole (Sequence (Load (Val r)) h2)) in
    let s4 = schedule [] [] (ContextStep Hole (Read r 7 h2 ())) in
    (| h2, L.Step s0 (L.Step s1 (L.Step s2 (L.Step s3 (L.Step s4 (L.Done _)))) ) |)

let loop_forever : thread = While (Val true) (Val ())

let main_without_join : expr [] TInt =
  Seq (Fork loop_forever) (Val 42)

let main_returns_before_child (h:M.heap)
  : L.execution language 2
      { L.threads = [Pack TInt main_without_join]; L.state = h }
      { L.threads = [Pack TInt (Val 42); Pack TUnit loop_forever]; L.state = h }
  = let s0 = schedule [] [] (ContextStep (SeqCtx Hole (Val 42)) (Spawn loop_forever h)) in
    let s1 = schedule [] [Pack TUnit loop_forever] (ContextStep Hole (Sequence (Val 42) h)) in
    L.Step s0 (L.Step s1 (L.Done _))

let looping_child_is_runnable (h:M.heap)
  : Lemma (L.reducible language (Pack TUnit loop_forever) h)
  = let s = ContextStep Hole (Unroll (Val true) (Val ()) h) in
    pack_step s;
    assert_norm (language.L.prim_step == packed_step);
    introduce exists e' h' spawned.
      packed_step (Pack TUnit loop_forever) h e' h' spawned
    with (Pack TUnit (If (Val true) (Seq (Val ()) loop_forever) (Val ()))) h [] and ()

let cas_worker (r:H.core_ref) : thread =
  Let (Cas (Val r) (Val 0) (Val 1)) (Val ())

let shared_cas (r:H.core_ref) : thread =
  Seq (Fork (cas_worker r)) (cas_worker r)

let interleaved_cas_run (r:H.core_ref) (h:H.full_hheap (M.points_to r 0))
  : h':H.full_heap u#3 & L.execution language 6
      { L.threads = [Pack TUnit (shared_cas r)]; L.state = h }
      { L.threads = [Pack TUnit (Val ()); Pack TUnit (Val ())]; L.state = h' }
  = M.points_to_contents r 0 h;
    let h' = M.write r 0 1 h in
    M.points_to_contents r 1 h';
    let worker = cas_worker r in
    let won : thread = Let (Val #[] #TBool true) (Val ()) in
    let lost : thread = Let (Val #[] #TBool false) (Val ()) in
    let s0 = schedule [] [] (ContextStep (SeqCtx Hole worker) (Spawn worker h)) in
    let s1 = schedule [] [Pack TUnit worker] (ContextStep Hole (Sequence worker h)) in
    let s2 = schedule [Pack TUnit worker] []
      (ContextStep (LetCtx Hole (Val ())) (CompareExchange r 0 1 true h h' ())) in
    let s3 = schedule [] [Pack TUnit won]
      (ContextStep (LetCtx Hole (Val ())) (CompareExchange r 0 1 false h' h' ())) in
    let s4 = schedule [Pack TUnit lost] []
      (ContextStep Hole (Beta true (Val ()) h')) in
    let s5 = schedule [] [Pack TUnit (Val ())]
      (ContextStep Hole (Beta false (Val ()) h')) in
    (| h', L.Step s0 (L.Step s1 (L.Step s2 (L.Step s3 (L.Step s4
        (L.Step s5 (L.Done _)))))) |)

// This is an operational state invariant, not yet a Pulse invariant assertion.
let shared_invariant (r:H.core_ref) (h:M.heap) : prop =
  M.contents h r 0 \/ M.contents h r 1

let cas_preserves_shared_invariant (r:H.core_ref) (h h':M.heap) (success:bool)
  : Lemma
      (requires shared_invariant r h /\ M.cas h r 0 1 success h')
      (ensures shared_invariant r h')
  = ()

let first_cas_succeeds (r:H.core_ref) (h h':M.heap) (success:bool)
  : Lemma
      (requires M.contents h r 0 /\ M.cas h r 0 1 success h')
      (ensures success /\ M.contents h' r 1)
  = eliminate exists old.
      M.contents h r old /\
      (if old = 0
       then success /\ H.extent h' == H.extent h /\
            M.contents h' r 1 /\ M.unchanged_except h h' r
       else not success /\ h' == h)
    with M.contents_unique h r 0 old

let second_cas_fails (r:H.core_ref) (h h':M.heap) (success:bool)
  : Lemma
      (requires M.contents h r 1 /\ M.cas h r 0 1 success h')
      (ensures not success /\ h' == h)
  = eliminate exists old.
      M.contents h r old /\
      (if old = 0
       then success /\ H.extent h' == H.extent h /\
            M.contents h' r 1 /\ M.unchanged_except h h' r
       else not success /\ h' == h)
    with M.contents_unique h r 1 old

let substitution_does_not_capture ()
  : Lemma (
      substitute 10
        (Let (Val #_ #TInt 20) (Add (Var (There Here)) (Var Here))) ==
      Let (Val #[] #TInt 20) (Add (Val 10) (Var Here)))
  = assert_norm (
      substitute 10
        (Let (Val #_ #TInt 20) (Add (Var (There Here)) (Var Here))) ==
      Let (Val #[] #TInt 20) (Add (Val 10) (Var Here)))

(** Shadowing may change the bound variable's type: the inner name is the
    loaded integer, whereas the load operand still names the outer reference. *)
let named_shadowing : expr [] TInt =
  let! cell = alloc (int_ 0) in
  let! cell = load cell in
  add cell (int_ 1)

let named_shadowing_expands ()
  : Lemma (named_shadowing ==
      Let (Alloc (Val 0)) (Let (Load (Var Here)) (Add (Var Here) (Val 1))))
  = assert_norm (named_shadowing ==
      Let (Alloc (Val 0)) (Let (Load (Var Here)) (Add (Var Here) (Val 1))))

(** Weakening shifts a free variable through BOTH the added context slot and
    the existing let binder, while preserving the internally bound variable. *)
let nested_binding : expr [TInt] TInt =
  let outer = Var Here in
  let! inner = int_ 20 in
  add (weaken outer) inner

let weakening_preserves_bound_variables ()
  : Lemma ((weaken nested_binding <: expr [TRef; TInt] TInt) ==
      Let (Val 20) (Add (Var (There (There Here))) (Var Here)))
  = assert_norm ((weaken nested_binding <: expr [TRef; TInt] TInt) ==
      Let (Val 20) (Add (Var (There (There Here))) (Var Here)))
