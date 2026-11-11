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
module Pulse.Extrinsic.ProofRejections

open Pulse.Extrinsic.HeapLang
module P = Pulse.Extrinsic.HeapLang.Proof
module R = Pulse.Extrinsic.Rules
module S = PulseCore.IndirectionTheorySep
module GS = Pulse.Lib.GhostSet

[@@expect_failure [19]]
let reopen (i:S.iref) (p pre:S.slprop) (e:expr [] TUnit) (q:P.post TUnit)
  (body:(unit -> Lemma (P.atomic (S.add_inv (S.add_inv GS.empty i) i)
    (S.star (P.exposed p) pre) e (P.prepend_post (P.exposed p) q))))
  = body ();
    P.atomic_invariant (S.add_inv GS.empty i) i p pre e q

[@@expect_failure [19]]
let escape_mask (i:S.iref) (p:S.slprop) (e:expr [] TUnit) (q:P.post TUnit)
  (body:(unit -> Lemma (P.atomic (S.add_inv GS.empty i) p e q)))
  = body ();
    P.atomic_to_hoare p e q

[@@expect_failure [19]]
let forget_body (i:S.iref) (p pre:S.slprop) (e:expr [] TUnit) (q:P.post TUnit)
  (body:(unit -> Lemma (P.atomic (S.add_inv GS.empty i) (S.star (P.exposed p) pre) e q)))
  = body ();
    P.atomic_invariant GS.empty i p pre e q

[@@expect_failure [19]]
let open_around_ordinary_triple (i:S.iref) (p pre:S.slprop) (e:expr [] TUnit) (q:P.post TUnit)
  (body:(unit -> Lemma (P.hoare (S.star (P.exposed p) pre) e (P.prepend_post (P.exposed p) q))))
  = body ();
    P.atomic_invariant GS.empty i p pre e q

[@@expect_failure [19]]
let update_without_credit (mask:S.inames) (p:S.slprop)
  : Lemma (P.update mask mask (S.later p) p)
  = P.update_later_elim mask p

[@@expect_failure [19]]
let escape_update (i:S.iref) (p:S.slprop)
  : Lemma (P.update GS.empty GS.empty (S.inv i p) (S.star (S.inv i p) (P.exposed p)))
  = P.open_invariant GS.empty i p

[@@expect_failure [19]]
let update_at_value (p q:S.slprop)
  (proof:(unit -> Lemma (P.update GS.empty GS.empty p q)))
  : Lemma (P.hoare p (Val ()) (P.constant_post q))
  = proof ();
    R.entails_refl q;
    P.value_rule q () (P.constant_post q);
    P.update_hoare p q (Val ()) (P.constant_post q)
