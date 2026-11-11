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
module Pulse.Extrinsic.AtomicLogic

(** Sound rules for the atomic source judgment. Structural rules transform
    framed enabled memories and the resources of every possible successor.
    The invariant rule invokes native open/close around the atomic obligation;
    updates generalizes this to arbitrary proved mask-changing ghost steps.
    Only [to_wp] imposes the closed-mask boundary required by ordinary WP. *)

module L = Pulse.Extrinsic.Language
module W = Pulse.Extrinsic.WP
module R = Pulse.Extrinsic.Rules
module A = Pulse.Extrinsic.Atomic
module S = PulseCore.IndirectionTheorySep
module U = Pulse.Extrinsic.Updates

let hoare l physical mask p e q =
  l.L.to_val e == None /\
  (forall f (m:S.full_mem). A.enabled mask p f m ==>
    step_post l physical mask e q f m)

let nonvalue l physical mask p e q = ()

let apply (p q f:S.slprop) (m:S.mem)
  : Lemma
      (requires S.level m > 0 /\ S.implies p q /\ S.interp (S.star p f) m)
      (ensures S.interp (S.star q f) m)
  = R.entails_refl f;
    R.entails_star p q f f;
    S.elim_implies (S.star p f) (S.star q f) m

let consequence l physical mask p p' e q q' =
  S.sep_laws ();
  introduce forall f (m:S.full_mem). A.enabled mask p' f m ==>
    step_post l physical mask e q' f m
  with (
    introduce A.enabled mask p' f m ==> step_post l physical mask e q' f m
    with (
      apply p' p (S.star f (S.mem_invariant mask m)) m;
      assert (step_post l physical mask e q f m);
      introduce forall e' s' spawned. l.L.prim_step e (physical m) e' s' spawned ==>
        result l physical mask q' f m e' s' spawned
      with (
        introduce l.L.prim_step e (physical m) e' s' spawned ==>
          result l physical mask q' f m e' s' spawned
        with (
          eliminate exists v (next:S.full_mem).
            l.L.to_val e' == Some v /\ spawned == [] /\ physical next == s' /\
            S.level next <= S.level m /\ S.budget next >= S.budget m /\
            S.inames_ok mask next /\
            S.interp (S.star (S.star (q v) f) (S.mem_invariant mask next)) next
          with (
            apply (q v) (q' v) (S.star f (S.mem_invariant mask next)) next;
            introduce exists v (next:S.full_mem).
              l.L.to_val e' == Some v /\ spawned == [] /\ physical next == s' /\
              S.level next <= S.level m /\ S.budget next >= S.budget m /\
              S.inames_ok mask next /\
              S.interp (S.star (S.star (q' v) f) (S.mem_invariant mask next)) next
            with v next and ()
          )
        )
      )
    )
  )

let frame_result (l:L.language) (physical:W.projection l) (mask:S.inames)
  (q:W.post l) (added f:S.slprop) (m:S.full_mem)
  (e':l.L.expr) (s':l.L.state) (spawned:list l.L.expr)
  : Lemma
      (requires result l physical mask q (S.star added f) m e' s' spawned)
      (ensures result l physical mask (W.framed_post l q added) f m e' s' spawned)
  = S.sep_laws ();
    eliminate exists v (next:S.full_mem).
      l.L.to_val e' == Some v /\ spawned == [] /\ physical next == s' /\
      S.level next <= S.level m /\ S.budget next >= S.budget m /\
      S.inames_ok mask next /\
      S.interp (S.star (S.star (q v) (S.star added f)) (S.mem_invariant mask next)) next
    with (
      introduce exists v (next:S.full_mem).
        l.L.to_val e' == Some v /\ spawned == [] /\ physical next == s' /\
        S.level next <= S.level m /\ S.budget next >= S.budget m /\
        S.inames_ok mask next /\
        S.interp (S.star (S.star (W.framed_post l q added v) f)
          (S.mem_invariant mask next)) next
      with v next and ()
    )

let frame l physical mask p e q added =
  S.sep_laws ();
  introduce forall f (m:S.full_mem). A.enabled mask (S.star p added) f m ==>
    step_post l physical mask e (W.framed_post l q added) f m
  with (
    introduce A.enabled mask (S.star p added) f m ==>
      step_post l physical mask e (W.framed_post l q added) f m
    with (
      assert (A.enabled mask p (S.star added f) m);
      assert (step_post l physical mask e q (S.star added f) m);
      introduce forall e' s' spawned. l.L.prim_step e (physical m) e' s' spawned ==>
        result l physical mask (W.framed_post l q added) f m e' s' spawned
      with (
        if l.L.prim_step e (physical m) e' s' spawned then
          frame_result l physical mask q added f m e' s' spawned
      )
    )
  )

let exists_pre #a l physical mask p e q =
  S.sep_laws ();
  introduce forall f (m:S.full_mem). A.enabled mask (S.op_exists_Star p) f m ==>
    step_post l physical mask e q f m
  with (
    introduce A.enabled mask (S.op_exists_Star p) f m ==>
      step_post l physical mask e q f m
    with (
      let tail = S.star f (S.mem_invariant mask m) in
      let owned, rest = S.split_mem (S.op_exists_Star p) tail m in
      S.interp_exists p;
      eliminate exists x. S.interp (p x) owned
      with (
        S.intro_star (p x) tail owned rest;
        assert (A.enabled mask (p x) f m)
      )
    )
  )

(** Open without changing the source heap, keep the invariant handle framed
    across the body, then close each possible successor. The exposed body is
    somewhere(later p), not p; clients must justify any stronger exposure. *)
let invariant l physical mask i p pre e post =
  S.sep_laws ();
  let inner = S.add_inv mask i in
  let body_pre = S.star (A.exposed p) pre in
  let body_post = A.exposed_post p post in
  introduce forall f (m:S.full_mem). A.enabled mask (S.star (S.inv i p) pre) f m ==>
    step_post l physical mask e (A.protected_post i p post) f m
  with (
    introduce A.enabled mask (S.star (S.inv i p) pre) f m ==>
      step_post l physical mask e (A.protected_post i p post) f m
    with (
      A.open_unchanged mask i p (S.star pre f) m;
      let _, opened = A.run (A.open_invariant mask i p) (S.star pre f) m in
      let body_frame = S.star (S.inv i p) f in
      assert (A.enabled inner body_pre body_frame m);
      assert (step_post l physical inner e body_post body_frame m);
      introduce forall e' s' spawned. l.L.prim_step e (physical m) e' s' spawned ==>
        result l physical mask (A.protected_post i p post) f m e' s' spawned
      with (
        introduce l.L.prim_step e (physical m) e' s' spawned ==>
          result l physical mask (A.protected_post i p post) f m e' s' spawned
        with (
          eliminate exists v (next:S.full_mem).
            l.L.to_val e' == Some v /\ spawned == [] /\ physical next == s' /\
            S.level next <= S.level m /\ S.budget next >= S.budget m /\
            S.inames_ok inner next /\
            S.interp (S.star (S.star (body_post v) body_frame) (S.mem_invariant inner next)) next
          with (
            A.close_unchanged mask i p (S.star (post v) f) next;
            let _, closed = A.run (A.close_invariant mask i p) (S.star (post v) f) next in
            introduce exists v (next:S.full_mem).
              l.L.to_val e' == Some v /\ spawned == [] /\ physical next == s' /\
              S.level next <= S.level m /\ S.budget next >= S.budget m /\
              S.inames_ok mask next /\
              S.interp (S.star (S.star (A.protected_post i p post v) f)
                (S.mem_invariant mask next)) next
            with v closed and ()
          )
        )
      )
    )
  )

(** The atomic proof preserves budget, even if ghost updates have lowered its
    level while spending existing credits. The source step now pays for exactly
    one additional aging, eliminating the postcondition's guard. Arbitrary
    higher-order resources can thus be transferred out of an invariant without
    a timelessness premise or a caller-supplied credit. *)
let to_wp_later l physical p e q =
  S.sep_laws ();
  W.children_nil l (W.wp_family l physical);
  W.wp_lift l physical p e q (fun f m ->
    S.inames_ok_empty m;
    assert (step_post l physical Pulse.Lib.GhostSet.empty e (later_post l q) f m);
    introduce forall e' s' spawned. l.L.prim_step e (physical m) e' s' spawned ==>
      (exists (m':S.full_mem).
        physical m' == s' /\ S.level m' < S.level m /\
        S.budget m' >= S.budget m - 1 /\
        S.interp (S.star (W.wp l physical e' q)
          (S.star (W.children l (W.wp_family l physical) spawned)
            (S.star f (W.invariant m')))) m')
    with (
      introduce l.L.prim_step e (physical m) e' s' spawned ==>
        (exists (m':S.full_mem).
          physical m' == s' /\ S.level m' < S.level m /\
          S.budget m' >= S.budget m - 1 /\
          S.interp (S.star (W.wp l physical e' q)
            (S.star (W.children l (W.wp_family l physical) spawned)
              (S.star f (W.invariant m')))) m')
      with (
        eliminate exists v (next:S.full_mem).
          l.L.to_val e' == Some v /\ spawned == [] /\ physical next == s' /\
          S.level next <= S.level m /\ S.budget next >= S.budget m /\
          S.inames_ok Pulse.Lib.GhostSet.empty next /\
          S.interp (S.star (S.star (S.later (q v)) f)
            (S.mem_invariant Pulse.Lib.GhostSet.empty next)) next
        with (
          R.age_later_resources (q v) f next;
          let final = S.age_mem next in
          W.wp_value l physical e' v q;
          introduce exists (m':S.full_mem).
            physical m' == s' /\ S.level m' < S.level m /\
            S.budget m' >= S.budget m - 1 /\
            S.interp (S.star (W.wp l physical e' q)
              (S.star (W.children l (W.wp_family l physical) spawned)
                (S.star f (W.invariant m')))) m'
          with final and ()
        )
      )
    ))

let to_wp l physical p e q =
  R.entails_refl p;
  introduce forall v. S.implies (q v) (later_post l q v)
  with R.entails_later (q v);
  consequence l physical Pulse.Lib.GhostSet.empty p p e q (later_post l q);
  to_wp_later l physical p e q

let lift l physical mask p e q proof =
  introduce forall f (m:S.full_mem). A.enabled mask p f m ==>
    step_post l physical mask e q f m
  with (
    introduce A.enabled mask p f m ==> step_post l physical mask e q f m
    with proof f m
  )

let updates l physical outer inner p mid e q post =
  S.sep_laws ();
  introduce forall f (m:S.full_mem). A.enabled outer p f m ==>
    step_post l physical outer e post f m
  with (
    introduce A.enabled outer p f m ==> step_post l physical outer e post f m
    with (
      U.apply l physical outer inner p mid f m;
      eliminate exists (opened:S.full_mem). U.result l physical inner mid f m opened with (
        assert (A.enabled inner mid f opened);
        assert (step_post l physical inner e q f opened);
        introduce forall e' s' spawned. l.L.prim_step e (physical m) e' s' spawned ==>
          result l physical outer post f m e' s' spawned
        with (
          introduce l.L.prim_step e (physical m) e' s' spawned ==>
            result l physical outer post f m e' s' spawned
          with (
            eliminate exists v (next:S.full_mem).
              l.L.to_val e' == Some v /\ spawned == [] /\ physical next == s' /\
              S.level next <= S.level opened /\ S.budget next >= S.budget opened /\
              S.inames_ok inner next /\
              S.interp (S.star (S.star (q v) f) (S.mem_invariant inner next)) next
            with (
              U.apply l physical inner outer (q v) (post v) f next;
              eliminate exists (closed:S.full_mem). U.result l physical outer (post v) f next closed
              with (
                introduce exists v (next:S.full_mem).
                  l.L.to_val e' == Some v /\ spawned == [] /\ physical next == s' /\
                  S.level next <= S.level m /\ S.budget next >= S.budget m /\
                  S.inames_ok outer next /\
                  S.interp (S.star (S.star (post v) f) (S.mem_invariant outer next)) next
                with v closed and ()
              )
            )
          )
        )
      )
    )
  )
