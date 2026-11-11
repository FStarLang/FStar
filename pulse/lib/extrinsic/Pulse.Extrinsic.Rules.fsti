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
module Pulse.Extrinsic.Rules

module L = Pulse.Extrinsic.Language
module W = Pulse.Extrinsic.WP
module S = PulseCore.IndirectionTheorySep

let hoare (l:L.language) (physical:W.projection l)
  (p:S.slprop) (e:l.L.expr) (q:W.post l) : prop =
  S.implies p (W.wp l physical e q)

let age_stable (l:L.language) (physical:W.projection l) : prop =
  forall (m:S.full_mem). physical (S.age_mem m) == physical m

val age_resources (p:S.slprop) (m:S.full_mem)
  : Lemma
      (requires S.budget m > 0 /\ S.interp (S.star p (W.invariant m)) m)
      (ensures
        S.is_full (S.age_mem m) /\
        S.level (S.age_mem m) == S.level m - 1 /\
        S.budget (S.age_mem m) == S.budget m - 1 /\
        S.interp (S.star p (W.invariant (S.age_mem m))) (S.age_mem m))

let readonly_post (l:L.language) (physical:W.projection l)
  (e:l.L.expr) (q:W.post l) (frame:S.slprop) (m:S.full_mem) : prop =
  L.reducible l e (physical m) /\
  (forall e' s' spawned.
    l.L.prim_step e (physical m) e' s' spawned ==>
    s' == physical m /\
    S.interp
      (S.star (W.wp l physical e' q)
        (S.star (W.children l (W.wp_family l physical) spawned)
          (S.star frame (W.invariant m)))) m)

val wp_readonly (l:L.language) (physical:W.projection l)
  (p:S.slprop) (e:l.L.expr) (q:W.post l)
  (step: (frame:S.slprop -> m:S.full_mem ->
    Lemma
      (requires S.budget m > 0 /\
        S.interp (S.star p (S.star frame (W.invariant m))) m)
      (ensures readonly_post l physical e q frame m)))
  : Lemma
      (requires l.L.to_val e == None /\ age_stable l physical)
      (ensures hoare l physical p e q)

val entails_refl (p:S.slprop) : Lemma (S.implies p p)
val entails_trans (p q r:S.slprop)
  : Lemma (requires S.implies p q /\ S.implies q r) (ensures S.implies p r)
val entails_emp (p:S.slprop) : Lemma (S.implies p S.emp)
val entails_fact (p:S.slprop) (fact:prop)
  : Lemma (requires fact) (ensures S.implies p (S.pure fact))
val fact_emp (fact:prop)
  : Lemma (requires fact) (ensures S.pure fact == S.emp)
val entails_star (p p' q q':S.slprop)
  : Lemma
      (requires S.implies p p' /\ S.implies q q')
      (ensures S.implies (S.star p q) (S.star p' q'))

val hoare_frame (l:L.language) (physical:W.projection l)
  (p:S.slprop) (e:l.L.expr) (q:W.post l) (frame:S.slprop)
  : Lemma
      (requires hoare l physical p e q)
      (ensures hoare l physical (S.star p frame) e (W.framed_post l q frame))

val hoare_consequence (l:L.language) (physical:W.projection l)
  (p p':S.slprop) (e:l.L.expr) (q q':W.post l)
  : Lemma
      (requires S.implies p' p /\ hoare l physical p e q /\
        (forall v. S.implies (q v) (q' v)))
      (ensures hoare l physical p' e q')

val entails_false (p:S.slprop) : Lemma (S.implies (S.pure False) p)

val hoare_pure (l:L.language) (physical:W.projection l)
  (p:S.slprop) (fact:prop) (e:l.L.expr) (q:W.post l)
  (proof:(unit -> Lemma (requires fact) (ensures hoare l physical p e q)))
  : Lemma (hoare l physical (S.star p (S.pure fact)) e q)

val entails_pure (p q:prop)
  : Lemma (requires p ==> q) (ensures S.implies (S.pure p) (S.pure q))

val entails_later (p:S.slprop) : Lemma (S.implies p (S.later p))
val exposed_inv (i:S.iref) (p:S.slprop)
  : Lemma (S.somewhere (S.later (S.inv i p)) == S.later (S.inv i p))
