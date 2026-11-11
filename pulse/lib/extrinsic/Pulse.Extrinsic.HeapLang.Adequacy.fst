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

let adequate_points_to (#t:ty) (r:H.core_ref) (initial:int)
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
  = points_to_realizable r initial h;
    adequate (C.points_to r initial) e q phi h run
