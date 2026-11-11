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

open Pulse.Extrinsic.HeapLang
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module E = Pulse.Extrinsic.HeapLang.Semantics
module M = Pulse.Extrinsic.HeapLang.Memory
module S = PulseCore.IndirectionTheorySep
module L = Pulse.Extrinsic.Language
module H = PulseCore.Heap

val realizable (h:M.heap) (p:S.slprop) : prop

val points_to_realizable (r:H.core_ref) (v:int) (h:H.full_heap u#3)
  : Lemma (requires H.interp (M.points_to r v) h)
      (ensures realizable h (C.points_to r v))

let pure_post (#t:ty) (phi:value t -> prop) (v:value t) = S.pure (phi v)

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

val adequate_points_to (#t:ty) (r:H.core_ref) (initial:int)
  (e:expr [] t) (q:P.post t) (phi:value t -> prop) (h:H.full_heap u#3)
  (#n:nat) (#last:L.config E.language)
  (run:L.execution E.language n
    ({ L.threads = [E.Pack t e]; L.state = h }) last)
  : Lemma
      (requires H.interp (M.points_to r initial) h /\
        P.hoare (C.points_to r initial) e q /\
        (forall v. S.implies (q v) (S.pure (phi v))))
      (ensures L.safe E.language last /\
        (forall result. L.main_returns E.language last result ==>
          exists (v:value t). result == E.PackValue t v /\ phi v))
