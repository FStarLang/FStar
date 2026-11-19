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
module Pulse.Extrinsic.MaskExamples

(** Clients of explicit mask updates rather than the convenient invariant rule.
    allocate_two composes ghost allocations with framing. read_with_updates
    opens a name, exposes physical ownership, performs one atomic source load,
    and restores the exposed body before closing. allocate_and_read combines
    ghost initialization and that source triple before a non-value.
    The value/non-value boundary matters: these rules do not add updates to
    the postcondition of an already-returned value. *)

open Pulse.Extrinsic.HeapLang
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module R = Pulse.Extrinsic.Rules
module S = PulseCore.IndirectionTheorySep
module GS = Pulse.Lib.GhostSet

let allocate_two (p q:S.slprop)
  : Lemma (P.update GS.empty GS.empty (S.star p q)
      (S.star (P.allocated p) (P.allocated q)))
  = S.sep_laws ();
    P.update_allocate p;
    P.update_frame GS.empty GS.empty p (P.allocated p) q;
    P.update_allocate q;
    P.update_frame GS.empty GS.empty q (P.allocated q) (P.allocated p);
    P.update_trans GS.empty GS.empty GS.empty
      (S.star p q) (S.star (P.allocated p) q) (S.star (P.allocated p) (P.allocated q))

(** Opening changes the mask, not the physical state. The handle is framed
    across the load; the returned value fact is framed across closing. *)
let read_with_updates (r:PulseCore.Heap.core_ref) (old:int) (i:S.iref)
  : Lemma (P.hoare (S.inv i (C.points_to r old)) (Load (Val r))
      (P.prepend_post (S.inv i (C.points_to r old)) (P.returns_value old)))
  = let body = C.points_to r old in
    let handle = S.inv i body in
    let mask = S.add_inv GS.empty i in
    let opened = S.star handle (P.exposed body) in
    let mid = S.star body handle in
    let e = Load (Val r) in
    let q = P.framed_post (P.read_post r old) handle in
    let post = P.prepend_post handle (P.returns_value old) in
    S.sep_laws ();
    C.points_to_exposed r old;
    R.entails_refl handle;
    R.entails_star handle handle (P.exposed body) body;
    P.open_invariant GS.empty i body;
    P.update_entails mask opened mid;
    P.update_trans GS.empty mask mask handle opened mid;
    P.atomic_load mask r old;
    P.atomic_frame mask body e (P.read_post r old) handle;
    P.close_invariant GS.empty i body;
    introduce forall v. P.update mask GS.empty (q v) (post v) with (
      let closing = S.star opened (P.returns_value old v) in
      R.entails_refl (P.returns_value old v);
      R.entails_star body (P.exposed body) handle handle;
      R.entails_star (S.star body handle) opened
        (P.returns_value old v) (P.returns_value old v);
      P.update_entails mask (q v) closing;
      P.update_frame mask GS.empty opened handle (P.returns_value old v);
      P.update_trans mask mask GS.empty (q v) closing (post v)
    );
    P.atomic_updates GS.empty mask handle mid e q post;
    P.atomic_to_hoare handle e post

let allocate_and_read (r:PulseCore.Heap.core_ref) (old:int)
  : Lemma (P.hoare (C.points_to r old) (Load (Val r)) (P.returns_value old))
  = let body = C.points_to r old in
    let e = Load (Val r) in
    let q = P.returns_value old in
    let target = P.wp e q in
    S.sep_laws ();
    P.update_allocate body;
    introduce forall (i:S.iref). P.update GS.empty GS.empty (S.inv i body) target with (
      let handle = S.inv i body in
      read_with_updates r old i;
      R.entails_refl handle;
      introduce forall v. S.implies (P.prepend_post handle q v) (q v) with (
        R.entails_emp handle;
        R.entails_refl (q v);
        R.entails_star handle S.emp (q v) (q v)
      );
      P.consequence handle handle e (P.prepend_post handle q) q;
      P.update_entails GS.empty handle target
    );
    P.update_exists GS.empty GS.empty (fun (i:S.iref) -> S.inv i body) target;
    P.update_trans GS.empty GS.empty GS.empty body (P.allocated body) target;
    R.entails_refl target;
    P.update_hoare body target e q
