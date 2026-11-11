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
let entails_left p q =
  S.implies_intro (S.star p q) p (fun h ->
    let owned, _ = S.star_elim p q h in
    S.reveal_slprop_ok ();
    S.mem_le_iff owned h)
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

let pure_elim p q fact proof =
  S.implies_intro (S.star p (S.pure fact)) q (fun h ->
    let owned, pure = S.star_elim p (S.pure fact) h in
    proof ();
    S.reveal_slprop_ok ();
    S.mem_le_iff owned h)

let exists_intro #a p x =
  S.implies_intro (p x) (S.op_exists_Star p) (fun h ->
    introduce exists (y:a). p y h with x and ())

let exists_elim #a p q =
  S.implies_intro (S.op_exists_Star p) q (fun h ->
    eliminate exists (x:a). p x h with ())

let exists_star #a p q =
  PulseCore.KnotInstantiation.mem_pred_ext
    (S.star (S.op_exists_Star p) q) (S.op_exists_Star (fun x -> S.star (p x) q))
    (fun h ->
      introduce S.star (S.op_exists_Star p) q h ==>
        S.op_exists_Star (fun x -> S.star (p x) q) h
      with (
        let owned, rest = S.star_elim (S.op_exists_Star p) q h in
        eliminate exists (x:a). p x owned with (
          S.star_intro (p x) q h owned rest;
          introduce exists (x':a). S.star (p x') q h with x and ()));
      introduce S.op_exists_Star (fun x -> S.star (p x) q) h ==>
        S.star (S.op_exists_Star p) q h
      with (
        eliminate exists (x:a). S.star (p x) q h with (
          let owned, rest = S.star_elim (p x) q h in
          introduce exists (y:a). p y owned with x and ();
          S.star_intro (S.op_exists_Star p) q h owned rest)))

let exists_swap #a #b p =
  PulseCore.KnotInstantiation.mem_pred_ext
    (S.op_exists_Star (fun x -> S.op_exists_Star (p x)))
    (S.op_exists_Star (fun y -> S.op_exists_Star (fun x -> p x y)))
    (fun h ->
      assert_norm (S.op_exists_Star (fun x -> S.op_exists_Star (p x)) h ==
        (exists (x:a) (y:b). p x y h));
      assert_norm (S.op_exists_Star (fun y -> S.op_exists_Star (fun x -> p x y)) h ==
        (exists (y:b) (x:a). p x y h)))

let with_pure p fact =
  S.sep_laws ();
  S.implies_intro p (S.star p (S.pure fact)) (fun h ->
    let owned, rest = S.star_elim p S.emp h in
    S.star_intro p (S.pure fact) h owned rest)

let entails_exposed p =
  S.implies_intro p (S.somewhere (S.later p)) (fun h ->
    S.reveal_slprop_ok ();
    S.set_loc_current_loc h;
    introduce exists loc. S.on loc (S.later p) h
    with (PulseCore.KnotInstantiation.current_loc_ h) and ())

let exposed_star p q =
  S.later_star p q;
  S.implies_intro (S.somewhere (S.later (S.star p q))) (S.star p q) (fun h ->
    eliminate exists loc. S.on loc (S.later (S.star p q)) h with (
      S.on_star_eq loc (S.later p) (S.later q);
      let a, b = S.star_elim (S.on loc (S.later p)) (S.on loc (S.later q)) h in
      introduce exists l. S.on l (S.later p) a with loc and ();
      introduce exists l. S.on l (S.later q) b with loc and ();
      S.star_intro p q h a b))

let exposed_pure fact =
  S.lift_pure_eq fact;
  S.timeless_pure fact;
  S.implies_intro (S.somewhere (S.later (S.pure fact))) (S.pure fact) (fun h ->
    eliminate exists loc. S.on loc (S.later (S.pure fact)) h with (
      S.on_later_eq loc (S.pure fact);
      S.on_lift_eq loc (PulseCore.MemoryAlt.pure fact)))

let exposed_exists #a p =
  S.later_exists p;
  S.implies_intro (S.somewhere (S.later (S.op_exists_Star p))) (S.op_exists_Star p)
    (fun h ->
      eliminate exists loc. S.on loc (S.later (S.op_exists_Star p)) h with (
        let located = S.set_loc_ h loc in
        assert (S.op_exists_Star (fun x -> S.later (p x)) located);
        eliminate exists (x:a). S.later (p x) located with (
          introduce exists l. S.on l (S.later (p x)) h with loc and ();
          introduce exists (y:a). p y h with x and ())))

let entails_later p =
  S.implies_intro p (S.later p) (fun _ -> S.reveal_slprop_ok ())

let age_later_resources p frame m =
  S.sep_laws ();
  let owned, rest = S.split_mem (S.later p) (S.star frame (W.invariant m)) m in
  let framed, closed = S.split_mem frame (W.invariant m) rest in
  S.age_level m;
  S.age_disjoint owned rest;
  S.age_disjoint framed closed;
  S.age_hereditary frame framed;
  S.mem_invariant_age Pulse.Lib.GhostSet.empty m closed;
  assert (S.interp p (S.age1 owned));
  S.intro_star frame (W.invariant (S.age_mem m)) (S.age1 framed) (S.age1 closed);
  S.intro_star p (S.star frame (W.invariant (S.age_mem m))) (S.age1 owned) (S.age1 rest)

let exposed_inv i p =
  PulseCore.KnotInstantiation.mem_pred_ext
    (S.somewhere (S.later (S.inv i p))) (S.later (S.inv i p)) (fun h ->
      assert_norm (S.somewhere (S.later (S.inv i p)) h ==
        (exists loc. S.on loc (S.later (S.inv i p)) h));
      introduce forall loc. S.on loc (S.later (S.inv i p)) == S.later (S.inv i p)
      with (S.on_later_eq loc (S.inv i p); S.on_inv_eq loc i p);
      introduce S.later (S.inv i p) h ==> S.somewhere (S.later (S.inv i p)) h with (
        introduce exists loc. S.on loc (S.later (S.inv i p)) h
        with Pulse.Lib.Loc.dummy_loc and ()))
