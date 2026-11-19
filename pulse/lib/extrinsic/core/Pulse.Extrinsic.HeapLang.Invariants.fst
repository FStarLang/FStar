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
module Pulse.Extrinsic.HeapLang.Invariants

(** A locality wrapper around the existing native invariant, not a new model.
    loc is duplicable and loc(l) ** p = loc(l) ** on(l,p). That equation
    transports exposed and restored bodies while the handle remains framed.
    Allocation chooses the actual current locality, keeping p unrestricted. *)

open Pulse.Extrinsic.HeapLang
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module R = Pulse.Extrinsic.Rules
module GS = Pulse.Lib.GhostSet

let duplicate i p =
  S.sep_laws ();
  introduce forall l. at i p l == S.star (at i p l) (at i p l)
  with (
    S.dup_inv_equiv i (S.on l p);
    S.loc_dup_eq l
  );
  R.duplicate_exists (at i p)

let atomic #t mask i p pre e q =
  S.sep_laws ();
  P.atomic_nonvalue (S.add_inv mask i) (S.star (S.later p) pre) e
    (P.prepend_post (S.later p) q);
  introduce forall l. P.atomic mask (S.star (at i p l) pre) e (P.prepend_post (inv i p) q)
  with (
    let here = S.loc l in
    let stored = S.on l p in
    let inner = S.add_inv mask i in
    let raw = P.prepend_post (S.later p) q in
    let framed = P.framed_post raw here in
    let tail = S.star here pre in
    let restored = P.prepend_post (P.exposed stored) (P.prepend_post here q) in
    R.exposed_on l p;
    S.on_later_eq l p;
    S.loc_on_eq l (S.later p);
    P.atomic_frame inner (S.star (S.later p) pre) e raw here;
    R.entails_refl (S.star (P.exposed stored) tail);
    introduce forall v. S.implies (framed v) (restored v)
    with R.entails_refl (restored v);
    P.atomic_consequence inner (S.star (S.star (S.later p) pre) here)
      (S.star (P.exposed stored) tail) e framed restored;
    P.atomic_invariant mask i stored tail e (P.prepend_post here q);
    R.entails_refl (S.star (at i p l) pre);
    introduce forall v. S.implies
      (P.prepend_post (S.inv i stored) (P.prepend_post here q) v)
      (P.prepend_post (inv i p) q v)
    with (
      R.exists_intro (at i p) l;
      R.entails_refl (q v);
      R.entails_star (at i p l) (inv i p) (q v) (q v)
    );
    P.atomic_consequence mask (S.star (at i p l) pre) (S.star (at i p l) pre) e
      (P.prepend_post (S.inv i stored) (P.prepend_post here q)) (P.prepend_post (inv i p) q)
  );
  P.atomic_exists mask (fun l -> S.star (at i p l) pre) e (P.prepend_post (inv i p) q);
  R.exists_star (at i p) pre

let allocate #t p pre e q proof =
  S.sep_laws ();
  let localized l = S.star (S.on l p) (S.loc l) in
  introduce forall l. P.hoare (S.star (localized l) pre) e q
  with (
    P.allocate_invariant (S.on l p) (S.star (S.loc l) pre) e q (fun i ->
      proof i;
      R.exists_intro (at i p) l;
      R.entails_refl pre;
      R.entails_star (at i p l) (inv i p) pre pre;
      R.entails_trans (S.star (at i p l) pre) (S.star (inv i p) pre) (P.wp e q)
    )
  );
  R.exists_elim (fun l -> S.star (localized l) pre) (P.wp e q);
  R.exists_star localized pre;
  R.localize p;
  R.entails_refl pre;
  R.entails_star p (S.op_exists_Star localized) pre pre;
  R.entails_trans (S.star p pre) (S.star (S.op_exists_Star localized) pre) (P.wp e q)
