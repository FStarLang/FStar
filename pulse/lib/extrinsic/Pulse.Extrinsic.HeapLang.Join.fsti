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

// 0: pending; 1: resource available; 2: resource claimed.
let phase = n:int{n == 0 \/ n == 1 \/ n == 2}
val body (flag:H.core_ref) (payload:S.slprop) : S.slprop
let handle (i:S.iref) (flag:H.core_ref) (payload:S.slprop) = S.inv i (body flag payload)

let signal_at (#g:list ty) (flag:expr g TRef) : expr g TUnit = Store flag (Val 1)
let wait_at (#g:list ty) (flag:expr g TRef) : expr g TUnit =
  While (If (Cas flag (Val 1) (Val 2)) (Val false) (Val true)) (Val ())
let signal (flag:H.core_ref) = signal_at (Val #[] flag)
let wait (flag:H.core_ref) = wait_at (Val #[] flag)

val initialize (flag:H.core_ref) (payload:S.slprop)
  : Lemma (S.implies (Pulse.Extrinsic.HeapLang.Logic.points_to flag 0) (body flag payload))
val initialize_ready (flag:H.core_ref) (payload:S.slprop)
  : Lemma (S.implies (S.star (Pulse.Extrinsic.HeapLang.Logic.points_to flag 1) payload)
      (body flag payload))
val signal_correct (i:S.iref) (flag:H.core_ref) (payload:S.slprop)
  : Lemma
      (requires S.implies (P.exposed payload) payload)
      (ensures P.hoare (S.star (handle i flag payload) payload) (signal flag)
        (P.constant_post (handle i flag payload)))
val wait_correct (i:S.iref) (flag:H.core_ref) (payload:S.slprop)
  : Lemma
      (requires S.implies (P.exposed payload) payload)
      (ensures P.hoare (handle i flag payload) (wait flag)
        (P.constant_post (S.star (handle i flag payload) payload)))
