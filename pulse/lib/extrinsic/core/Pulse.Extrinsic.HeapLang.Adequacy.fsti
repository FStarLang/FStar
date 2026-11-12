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

(** Uniform soundness of the typed source-proof interface.
    realizable means that precondition resources and the ambient invariant can
    be installed over the given physical heap at every requested budget.
    sound combines execution existence, safety of all finite prefixes, and
    the pure property of every returned main-thread value, without requiring
    an execution argument. adequate observes a particular execution.
    safe_execution and can_run are safety-only conveniences.

    emp_realizable and points_to_realizable handle common initial resources.
    Clients end with Hoare triples: they need no per-program trace induction,
    logical-world constructor, or budget argument. This is partial correctness,
    not termination, fairness, or a claim that all children have joined. *)

open Pulse.Extrinsic.HeapLang
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module E = Pulse.Extrinsic.HeapLang.Semantics
module M = Pulse.Extrinsic.HeapLang.Memory
module S = PulseCore.IndirectionTheorySep
module L = Pulse.Extrinsic.Language
module H = PulseCore.Heap

val realizable (h:M.heap) (p:S.slprop) : prop

(** Initialization lemmas for the same realizable predicate, not separate
    notions of soundness. emp requires no owned cells, not an empty heap. *)
val emp_realizable (h:H.full_heap u#3)
  : Lemma (realizable h S.emp)

val points_to_realizable (r:H.core_ref) (v:int) (h:H.full_heap u#3)
  : Lemma (requires H.interp (M.points_to r v) h)
      (ensures realizable h (C.points_to r v))

let pure_post (#t:ty) (phi:value t -> prop) (v:value t) = S.pure (phi v)

(** Execution existence for every finite horizon, and safety/result correctness
    for EVERY execution, not just the witnesses provided by runs_for.
    The result clause applies as soon as the main thread returns, even if
    children are still running; early termination in runs_for requires all
    threads to have returned. *)
let execution_correct (#t:ty) (e:expr [] t) (h:M.heap) (phi:value t -> prop) : prop =
  let initial = { L.threads = [E.Pack t e]; L.state = h } in
  (forall (n:nat). L.runs_for E.language n initial) /\
  (forall (n:nat) (last:L.config E.language) (run:L.execution E.language n initial last).
    L.safe E.language last /\
    (forall result. L.main_returns E.language last result ==>
      exists (v:value t). result == E.PackValue t v /\ phi v))

val adequate (#t:ty) (p:S.slprop) (e:expr [] t) (q:P.post t) (phi:value t -> prop) (h:M.heap)
  (#n:nat) (#last:L.config E.language)
  (run:L.execution E.language n
    ({ L.threads = [E.Pack t e]; L.state = h }) last)
  : Lemma
      (requires realizable h p /\ P.hoare p e q /\
        (forall v. S.implies (q v) (S.pure (phi v))))
      (ensures L.safe E.language last /\
        (forall result. L.main_returns E.language last result ==>
          exists (v:value t). result == E.PackValue t v /\ phi v))

(** Every finite execution prefix is safe, under every operational choice.
    No execution, pure observation, or new triple for a reduct is required. *)
val safe_execution (#t:ty) (p:S.slprop) (e:expr [] t) (q:P.post t) (h:M.heap)
  : Lemma
      (requires realizable h p /\ P.hoare p e q)
      (ensures L.safe_execution E.language { L.threads = [E.Pack t e]; L.state = h })

(** Run for n scheduler steps, or finish all threads sooner. Realizability
    supplies every finite budget; this does not assert eventual termination. *)
val can_run (#t:ty) (p:S.slprop) (e:expr [] t) (q:P.post t) (h:M.heap) (n:nat)
  : Lemma
      (requires realizable h p /\ P.hoare p e q)
      (ensures L.runs_for E.language n { L.threads = [E.Pack t e]; L.state = h })

(** Complete soundness corollary: no execution argument, with the observable
    consequence of Q retained at every returning prefix. *)
val sound (#t:ty) (p:S.slprop) (e:expr [] t) (q:P.post t)
  (phi:value t -> prop) (h:M.heap)
  : Lemma
      (requires realizable h p /\ P.hoare p e q /\
        (forall v. S.implies (q v) (S.pure (phi v))))
      (ensures execution_correct e h phi)

(** Uniform adequacy for the update-closed WP, including programs which are
    already values. Final ghost updates preserve the observed source heap. *)
val adequate_fancy (#t:ty) (p:S.slprop) (e:expr [] t) (q:P.post t)
  (phi:value t -> prop) (h:M.heap)
  (#n:nat) (#last:L.config E.language)
  (run:L.execution E.language n
    ({ L.threads = [E.Pack t e]; L.state = h }) last)
  : Lemma
      (requires realizable h p /\ Pulse.Extrinsic.HeapLang.FancyProof.hoare p e q /\
        (forall v. S.implies (q v) (S.pure (phi v))))
      (ensures L.safe E.language last /\
        (forall result. L.main_returns E.language last result ==>
          exists (v:value t). result == E.PackValue t v /\ phi v))

(** The same execution corollaries for update-closed triples. *)
val safe_execution_fancy (#t:ty) (p:S.slprop) (e:expr [] t) (q:P.post t) (h:M.heap)
  : Lemma
      (requires realizable h p /\ Pulse.Extrinsic.HeapLang.FancyProof.hoare p e q)
      (ensures L.safe_execution E.language { L.threads = [E.Pack t e]; L.state = h })

val can_run_fancy (#t:ty) (p:S.slprop) (e:expr [] t) (q:P.post t) (h:M.heap) (n:nat)
  : Lemma
      (requires realizable h p /\ Pulse.Extrinsic.HeapLang.FancyProof.hoare p e q)
      (ensures L.runs_for E.language n { L.threads = [E.Pack t e]; L.state = h })

val sound_fancy (#t:ty) (p:S.slprop) (e:expr [] t) (q:P.post t)
  (phi:value t -> prop) (h:M.heap)
  : Lemma
      (requires realizable h p /\ Pulse.Extrinsic.HeapLang.FancyProof.hoare p e q /\
        (forall v. S.implies (q v) (S.pure (phi v))))
      (ensures execution_correct e h phi)
