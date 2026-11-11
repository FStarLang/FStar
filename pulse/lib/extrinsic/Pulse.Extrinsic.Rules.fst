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
friend PulseCore.IndirectionTheorySep

open FStar.Ghost
module L = Pulse.Extrinsic.Language
module W = Pulse.Extrinsic.WP
module S = PulseCore.IndirectionTheorySep

let age_resources (p:S.slprop) (m:S.full_mem)
  : Lemma
      (requires S.budget m > 0 /\ S.interp (S.star p (W.invariant m)) m)
      (ensures
        S.is_full (S.age_mem m) /\
        S.level (S.age_mem m) == S.level m - 1 /\
        S.budget (S.age_mem m) == S.budget m - 1 /\
        S.interp (S.star p (W.invariant (S.age_mem m))) (S.age_mem m))
  = let owned, closed = S.split_mem p (W.invariant m) m in
    S.age_level m;
    S.age_disjoint owned closed;
    S.age_hereditary p owned;
    S.mem_invariant_age Pulse.Lib.GhostSet.empty m closed;
    S.intro_star p (W.invariant (S.age_mem m)) (S.age1 owned) (S.age1 closed)

// The state is unchanged, but ownership may be transferred to spawned threads.
let wp_readonly (l:L.language) (physical:W.projection l)
  (p:S.slprop) (e:l.L.expr) (q:W.post l)
  (step: (frame:S.slprop -> m:S.full_mem ->
    Lemma
      (requires S.budget m > 0 /\
        S.interp (S.star p (S.star frame (W.invariant m))) m)
      (ensures readonly_post l physical e q frame m)))
  : Lemma
      (requires l.L.to_val e == None /\ age_stable l physical)
      (ensures hoare l physical p e q)
  = W.wp_lift l physical p e q (fun frame m ->
      S.sep_laws ();
      step frame m;
      introduce forall e' s' spawned.
        l.L.prim_step e (physical m) e' s' spawned ==>
        (exists (m':S.full_mem).
          physical m' == s' /\
          S.level m' < S.level m /\
          S.budget m' >= S.budget m - 1 /\
          S.interp
            (S.star (W.wp l physical e' q)
              (S.star (W.children l (W.wp_family l physical) spawned)
                (S.star frame (W.invariant m')))) m')
      with (
        introduce l.L.prim_step e (physical m) e' s' spawned ==>
          (exists (m':S.full_mem).
            physical m' == s' /\
            S.level m' < S.level m /\
            S.budget m' >= S.budget m - 1 /\
            S.interp
              (S.star (W.wp l physical e' q)
                (S.star (W.children l (W.wp_family l physical) spawned)
                  (S.star frame (W.invariant m')))) m')
        with (
          age_resources
            (S.star (W.wp l physical e' q)
              (S.star (W.children l (W.wp_family l physical) spawned) frame)) m;
          introduce exists (m':S.full_mem).
            physical m' == s' /\
            S.level m' < S.level m /\
            S.budget m' >= S.budget m - 1 /\
            S.interp
              (S.star (W.wp l physical e' q)
                (S.star (W.children l (W.wp_family l physical) spawned)
                  (S.star frame (W.invariant m')))) m'
          with (S.age_mem m) and ()
        )
      ))

let entails_refl p = ()
let entails_trans p q r = ()
let entails_emp p = ()
let entails_fact p fact = ()
let fact_emp fact =
  PulseCore.KnotInstantiation.mem_pred_ext (S.pure fact) S.emp (fun _ -> ())
let entails_star p p' q q' =
  S.implies_intro (S.star p q) (S.star p' q') (fun h ->
    let h1, h2 = S.star_elim p q h in
    S.star_intro p' q' h h1 h2)

let hoare_frame l physical p e q frame =
  entails_refl frame;
  entails_star p (W.wp l physical e q) frame frame;
  W.wp_frame l physical e q frame;
  entails_trans (S.star p frame) (S.star (W.wp l physical e q) frame)
    (W.wp l physical e (W.framed_post l q frame))

let hoare_consequence l physical p p' e q q' =
  W.wp_mono l physical e q q';
  entails_trans p' p (W.wp l physical e q);
  entails_trans p' (W.wp l physical e q) (W.wp l physical e q')

let entails_false p = ()

let hoare_pure l physical p fact e q proof =
  S.implies_intro (S.star p (S.pure fact)) (W.wp l physical e q) (fun h ->
    let owned, pure = S.star_elim p (S.pure fact) h in
    proof ();
    S.reveal_slprop_ok ();
    S.mem_le_iff owned h)

let entails_pure p q = ()
