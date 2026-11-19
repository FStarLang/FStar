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

(** A verified SOURCE library for resource-transferring completion.
    Signal stores the ready state; wait retries CAS(ready, claimed) and returns
    the deposited payload exactly when it claims it. Payloads are arbitrary
    assertions, including invariant handles and WPs. A successful source CAS
    pays for eliminating the transferred payload's later guard.

    This is a flag protocol, not primitive scheduler join: it establishes that
    publication occurred, not that the child has taken its final return step.
    Repeated signal can republish a newly supplied payload; one-shot use in
    ParallelIncrement transfers the child's completed fractional receipt. *)

open Pulse.Extrinsic.HeapLang
open Pulse.Extrinsic.HeapLang.Notation
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module I = Pulse.Extrinsic.HeapLang.Invariants

// 0: pending; 1: resource available; 2: resource claimed.
let phase = n:int{n == 0 \/ n == 1 \/ n == 2}
val body (flag:H.core_ref) (payload:S.slprop) : S.slprop
let handle (i:S.iref) (flag:H.core_ref) (payload:S.slprop) = I.inv i (body flag payload)

let signal_at (#g:list ty) (flag:expr g TRef) : expr g TUnit = store flag (int_ 1)
let wait_at (#g:list ty) (flag:expr g TRef) : expr g TUnit =
  while_ (if_ (cas flag (int_ 1) (int_ 2)) (bool_ false) (bool_ true)) unit_
let signal (flag:H.core_ref) = signal_at (Val #[] flag)
let wait (flag:H.core_ref) = wait_at (Val #[] flag)

val initialize (flag:H.core_ref) (payload:S.slprop)
  : Lemma (S.implies (Pulse.Extrinsic.HeapLang.Logic.points_to flag 0) (body flag payload))
val initialize_ready (flag:H.core_ref) (payload:S.slprop)
  : Lemma (S.implies (S.star (Pulse.Extrinsic.HeapLang.Logic.points_to flag 1) payload)
      (body flag payload))
val signal_correct (i:S.iref) (flag:H.core_ref) (payload:S.slprop)
  : Lemma
      (ensures P.hoare (S.star (handle i flag payload) payload) (signal flag)
        (P.constant_post (handle i flag payload)))
(** A successful claim removes the payload from the invariant; failure leaves
    it untouched and retries. Only partial correctness is promised. *)
val wait_correct (i:S.iref) (flag:H.core_ref) (payload:S.slprop)
  : Lemma
      (ensures P.hoare (handle i flag payload) (wait flag)
        (P.constant_post (S.star (handle i flag payload) payload)))
