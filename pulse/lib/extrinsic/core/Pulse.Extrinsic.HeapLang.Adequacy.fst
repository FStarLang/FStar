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
module Pulse.Extrinsic.HeapLang.Adequacy

(** Instantiate generic thread-pool adequacy with the typed HeapLang WP.
    Realizability supplies a world at budget n+1 for any n-step execution.
    Consequence turns the typed postcondition into the observable pure fact;
    packing transports it through generic adequacy and is then eliminated.
    Initialization via world is shared once, never repeated in example proofs. *)
friend Pulse.Extrinsic.HeapLang.Proof

open Pulse.Extrinsic.HeapLang
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module E = Pulse.Extrinsic.HeapLang.Semantics
module M = Pulse.Extrinsic.HeapLang.Memory
module S = PulseCore.IndirectionTheorySep
module W = Pulse.Extrinsic.WP
module A = Pulse.Extrinsic.Adequacy
module L = Pulse.Extrinsic.Language
module H = PulseCore.Heap

let realizable (h:M.heap) (p:S.slprop) : prop =
  forall (budget:nat). exists (m:S.full_mem).
    C.physical m == h /\ S.budget m >= budget /\
    S.interp (S.star p (W.invariant m)) m

let emp_realizable h =
  introduce forall (budget:nat). exists (m:S.full_mem).
    C.physical m == h /\ S.budget m >= budget /\
    S.interp (S.star S.emp (W.invariant m)) m
  with (
    let m = C.world h budget in
    S.sep_laws ();
    S.emp_equiv m;
    introduce exists (m:S.full_mem).
      C.physical m == h /\ S.budget m >= budget /\
      S.interp (S.star S.emp (W.invariant m)) m
    with m and ()
  )

let points_to_realizable (r:H.core_ref) (v:int) (h:H.full_heap u#3)
  : Lemma (requires H.interp (M.points_to r v) h)
      (ensures realizable h (C.points_to r v))
  = introduce forall (budget:nat). exists (m:S.full_mem).
      C.physical m == h /\ S.budget m >= budget /\
      S.interp (S.star (C.points_to r v) (W.invariant m)) m
    with (
      let m = C.world h budget in
      C.points_to_intro r v m;
      S.sep_laws ();
      introduce exists (m:S.full_mem).
        C.physical m == h /\ S.budget m >= budget /\
        S.interp (S.star (C.points_to r v) (W.invariant m)) m
      with m and ()
    )

(** Discharge all source executions using the single generic pool theorem.
    The final packed type must equal t, since any other type has false as its
    packed postcondition. Unpacking recovers the client's typed result. *)
let adequate (#t:ty) (p:S.slprop) (e:expr [] t) (q:P.post t) (phi:value t -> prop) (h:M.heap)
  (#n:nat) (#last:L.config E.language)
  (run:L.execution E.language n
    ({ L.threads = [E.Pack t e]; L.state = h }) last)
  : Lemma
      (requires realizable h p /\ P.hoare p e q /\
        (forall v. S.implies (q v) (S.pure (phi v))))
      (ensures L.safe E.language last /\
        (forall result. L.main_returns E.language last result ==>
          exists (v:value t). result == E.PackValue t v /\ phi v))
  = Pulse.Extrinsic.Rules.entails_refl p;
    P.consequence p p e q (pure_post phi);
    let q = P.packed_post (pure_post phi) in
    S.sep_laws ();
    W.children_nil E.language (W.wp_family E.language C.physical);
    eliminate exists (m:S.full_mem).
      C.physical m == h /\ S.budget m >= n + 1 /\
      S.interp (S.star p (W.invariant m)) m
    with (
      Pulse.Extrinsic.HeapLang.Rules.apply_frame p (P.wp e (pure_post phi)) (W.invariant m) m;
      A.adequate E.language C.physical q run m;
      introduce forall result. L.main_returns E.language last result ==>
        (exists (v:value t). result == E.PackValue t v /\ phi v)
      with (
        introduce L.main_returns E.language last result ==>
          (exists (v:value t). result == E.PackValue t v /\ phi v)
        with (
          eliminate exists (next:S.full_mem).
            C.physical next == last.L.state /\ S.interp (q result) next
          with (
            let E.PackValue u v = result in
            if u = t then (
              S.interp_pure (phi v) next;
              introduce exists (v':value t). result == E.PackValue t v' /\ phi v'
              with v and ()
            ) else S.interp_pure False next
          )
        )
      )
    )

let safe_execution #t p e q h =
  let initial = { L.threads = [E.Pack t e]; L.state = h } in
  introduce forall v. S.implies (q v) (S.pure True)
  with Pulse.Extrinsic.Rules.entails_fact (q v) True;
  introduce forall (n:nat) (last:L.config E.language)
    (run:L.execution E.language n initial last). L.safe E.language last
  with adequate p e q (fun _ -> True) h run

let can_run #t p e q h n =
  safe_execution p e q h;
  L.safe_execution_runs E.language n { L.threads = [E.Pack t e]; L.state = h }

module FP = Pulse.Extrinsic.HeapLang.FancyProof
module F = Pulse.Extrinsic.FancyUpdates
module U = Pulse.Extrinsic.Updates
module R = Pulse.Extrinsic.Rules
module GS = Pulse.Lib.GhostSet

let adequate_fancy #t p e q phi h #n #last run =
  R.entails_refl p;
  FP.consequence p p e q (pure_post phi);
  let observed = P.packed_post (FP.modal_post (pure_post phi)) in
  S.sep_laws ();
  W.children_nil E.language (W.wp_family E.language C.physical);
  eliminate exists (m:S.full_mem).
    C.physical m == h /\ S.budget m >= n + 1 /\
    S.interp (S.star p (W.invariant m)) m
  with (
    Pulse.Extrinsic.HeapLang.Rules.apply_frame p (FP.wp e (pure_post phi)) (W.invariant m) m;
    A.preserve_execution E.language C.physical observed run m;
    eliminate exists (next:S.full_mem).
      A.represents E.language C.physical observed last next /\ S.budget next > 0
    with (
      A.pool_safe E.language C.physical observed last next;
      introduce forall result. L.main_returns E.language last result ==>
        (exists (v:value t). result == E.PackValue t v /\ phi v)
      with (
        introduce L.main_returns E.language last result ==>
          (exists (v:value t). result == E.PackValue t v /\ phi v)
        with (
          A.pool_result_with_invariant E.language C.physical observed last next result;
          let E.PackValue u v = result in
          if u = t then (
            let fact = S.pure (phi v) in
            F.elim E.language C.physical GS.empty GS.empty fact;
            S.inames_ok_empty next;
            U.apply E.language C.physical GS.empty GS.empty
              (FP.fupd GS.empty GS.empty fact) fact S.emp next;
            eliminate exists (final:S.full_mem).
              U.result E.language C.physical GS.empty fact S.emp next final
            with (
              S.destruct_star_l fact (W.invariant final) final;
              S.interp_pure (phi v) final;
              introduce exists (v':value t). result == E.PackValue t v' /\ phi v'
              with v and ()
            )
          ) else (
            S.destruct_star_l (S.pure False) (W.invariant next) next;
            S.interp_pure False next
          )
        )
      )
    )
  )

let safe_execution_fancy #t p e q h =
  let initial = { L.threads = [E.Pack t e]; L.state = h } in
  introduce forall v. S.implies (q v) (S.pure True)
  with R.entails_fact (q v) True;
  introduce forall (n:nat) (last:L.config E.language)
    (run:L.execution E.language n initial last). L.safe E.language last
  with adequate_fancy p e q (fun _ -> True) h run

let can_run_fancy #t p e q h n =
  safe_execution_fancy p e q h;
  L.safe_execution_runs E.language n { L.threads = [E.Pack t e]; L.state = h }
