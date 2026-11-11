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
module Pulse.Extrinsic.Updates

module L = Pulse.Extrinsic.Language
module W = Pulse.Extrinsic.WP
module S = PulseCore.IndirectionTheorySep
module A = Pulse.Extrinsic.Atomic
module R = Pulse.Extrinsic.Rules
module GS = Pulse.Lib.GhostSet

let hoare l physical before after p q =
  forall f (m:S.full_mem). enabled before p f m ==>
    exists (next:S.full_mem). result l physical after q f m next

let entails l physical mask p q =
  S.sep_laws ();
  introduce forall f (m:S.full_mem). enabled mask p f m ==>
    (exists (next:S.full_mem). result l physical mask q f m next)
  with (
    introduce enabled mask p f m ==>
      (exists (next:S.full_mem). result l physical mask q f m next)
    with (
      let tail = S.star f (S.mem_invariant mask m) in
      R.entails_refl tail;
      R.entails_star p q tail tail;
      S.elim_implies (S.star p tail) (S.star q tail) m;
      introduce exists (next:S.full_mem). result l physical mask q f m next with m and ()
    )
  )

let false_pre l physical before after q =
  S.sep_laws ();
  introduce forall f (m:S.full_mem). enabled before (S.pure False) f m ==>
    (exists (next:S.full_mem). result l physical after q f m next)
  with (
    if enabled before (S.pure False) f m then (
      S.destruct_star_l (S.pure False) (S.star f (S.mem_invariant before m)) m;
      S.interp_pure False m
    )
  )

let trans l physical before middle after p q r =
  introduce forall f (m:S.full_mem). enabled before p f m ==>
    (exists (next:S.full_mem). result l physical after r f m next)
  with (
    introduce enabled before p f m ==>
      (exists (next:S.full_mem). result l physical after r f m next)
    with (
      eliminate exists (mid:S.full_mem). result l physical middle q f m mid with (
        eliminate exists (next:S.full_mem). result l physical after r f mid next with (
          introduce exists (next:S.full_mem). result l physical after r f m next
          with next and ()
        )
      )
    )
  )

let frame_result (l:L.language) (physical:W.projection l) (after:S.inames)
  (q added f:S.slprop) (m next:S.full_mem)
  : Lemma
      (requires result l physical after q (S.star added f) m next)
      (ensures result l physical after (S.star q added) f m next)
  = S.sep_laws ();
    assert (enabled after q (S.star added f) next);
    assert (enabled after (S.star q added) f next)

let frame l physical before after p q added =
  S.sep_laws ();
  introduce forall f (m:S.full_mem). enabled before (S.star p added) f m ==>
    (exists (next:S.full_mem). result l physical after (S.star q added) f m next)
  with (
    introduce enabled before (S.star p added) f m ==>
      (exists (next:S.full_mem). result l physical after (S.star q added) f m next)
    with (
      assert (enabled before p (S.star added f) m);
      eliminate forall frame (m:S.full_mem). enabled before p frame m ==>
        (exists (next:S.full_mem). result l physical after q frame m next)
      with (S.star added f) m;
      eliminate exists (next:S.full_mem). result l physical after q (S.star added f) m next with (
        frame_result l physical after q added f m next;
        introduce exists (next:S.full_mem). result l physical after (S.star q added) f m next
        with next and ()
      )
    )
  )

let exists_pre #a l physical before after p q =
  S.sep_laws ();
  introduce forall f (m:S.full_mem). enabled before (S.op_exists_Star p) f m ==>
    (exists (next:S.full_mem). result l physical after q f m next)
  with (
    introduce enabled before (S.op_exists_Star p) f m ==>
      (exists (next:S.full_mem). result l physical after q f m next)
    with (
      let tail = S.star f (S.mem_invariant before m) in
      let owned, rest = S.split_mem (S.op_exists_Star p) tail m in
      S.interp_exists p;
      eliminate exists x. S.interp (p x) owned with (
        S.intro_star (p x) tail owned rest;
        assert (enabled before (p x) f m)
      )
    )
  )

let open_invariant l physical mask i p =
  S.sep_laws ();
  introduce forall f (m:S.full_mem). enabled mask (S.inv i p) f m ==>
    (exists (next:S.full_mem).
      result l physical (S.add_inv mask i) (S.star (S.inv i p) (A.exposed p)) f m next)
  with (
    introduce enabled mask (S.inv i p) f m ==>
      (exists (next:S.full_mem).
        result l physical (S.add_inv mask i) (S.star (S.inv i p) (A.exposed p)) f m next)
    with (
      A.open_unchanged mask i p f m;
      let _, next = A.run (A.open_invariant mask i p) f m in
      introduce exists (next:S.full_mem).
        result l physical (S.add_inv mask i) (S.star (S.inv i p) (A.exposed p)) f m next
      with next and ()
    )
  )

let close_invariant l physical mask i p =
  S.sep_laws ();
  introduce forall f (m:S.full_mem). enabled (S.add_inv mask i) (S.star (S.inv i p) (A.exposed p)) f m ==>
    (exists (next:S.full_mem). result l physical mask (S.inv i p) f m next)
  with (
    introduce enabled (S.add_inv mask i) (S.star (S.inv i p) (A.exposed p)) f m ==>
      (exists (next:S.full_mem). result l physical mask (S.inv i p) f m next)
    with (
      A.close_unchanged mask i p f m;
      let _, next = A.run (A.close_invariant mask i p) f m in
      introduce exists (next:S.full_mem). result l physical mask (S.inv i p) f m next
      with next and ()
    )
  )

let allocate l physical p ghost =
  S.sep_laws ();
  introduce forall f (m:S.full_mem). enabled GS.empty p f m ==>
    (exists (next:S.full_mem). result l physical GS.empty (allocated p) f m next)
  with (
    introduce enabled GS.empty p f m ==>
      (exists (next:S.full_mem). result l physical GS.empty (allocated p) f m next)
    with (
      let (| i, next |) = A.allocate_invariant p f m in
      ghost m next;
      S.inames_ok_empty next;
      let tail = S.star f (W.invariant next) in
      let owned, rest = S.split_mem (S.inv i p) tail next in
      S.interp_exists (fun (i:S.iref) -> S.inv i p);
      assert (S.interp (allocated p) owned);
      S.intro_star (allocated p) tail owned rest;
      introduce exists (next:S.full_mem). result l physical GS.empty (allocated p) f m next
      with next and ()
    )
  )

let later_elim l physical mask p ghost =
  S.sep_laws ();
  introduce forall f (m:S.full_mem). enabled mask (S.star (S.later p) (S.later_credit 1)) f m ==>
    (exists (next:S.full_mem). result l physical mask p f m next)
  with (
    introduce enabled mask (S.star (S.later p) (S.later_credit 1)) f m ==>
      (exists (next:S.full_mem). result l physical mask p f m next)
    with (
      let next = A.eliminate_later mask p f m in
      ghost m next;
      introduce exists (next:S.full_mem). result l physical mask p f m next
      with next and ()
    )
  )

let apply l physical before after p q f m = ()

let bind_wp l physical p mid e q =
  S.sep_laws ();
  W.wp_lift l physical p e q (fun f m ->
    S.inames_ok_empty m;
    assert (enabled GS.empty p f m);
    apply l physical GS.empty GS.empty p mid f m;
    eliminate exists (next:S.full_mem). result l physical GS.empty mid f m next with (
      let tail = S.star f (W.invariant next) in
      R.entails_refl tail;
      R.entails_star mid (W.wp l physical e q) tail tail;
      S.elim_implies (S.star mid tail) (S.star (W.wp l physical e q) tail) next;
      W.wp_step l physical e q f next
    ))
