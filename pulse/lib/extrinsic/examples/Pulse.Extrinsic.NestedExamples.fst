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
module Pulse.Extrinsic.NestedExamples

open Pulse.Extrinsic.HeapLang
module P = Pulse.Extrinsic.HeapLang.Proof
module B = Pulse.Extrinsic.ExamplePredicates
module I = Pulse.Extrinsic.InvariantExamples
module R = Pulse.Extrinsic.Rules
module S = PulseCore.IndirectionTheorySep
module GS = Pulse.Lib.GhostSet

let nested_open (r s:PulseCore.Heap.core_ref) (desired:B.bit)
  (i:S.iref) (j:S.iref{not (j == i)})
  : Lemma (P.hoare (S.star (S.inv i (B.bit_cell s)) (S.inv j (B.bit_cell r)))
      (Store (Val r) (Val desired))
      (P.constant_post (S.star (S.inv i (B.bit_cell s)) (S.inv j (B.bit_cell r)))))
  = let body = B.bit_cell s in
    let inner = S.inv j (B.bit_cell r) in
    let mask = S.add_inv GS.empty i in
    let e = Store (Val r) (Val desired) in
    let q = P.constant_post #TUnit inner in
    let exposed = P.exposed body in
    let pre = S.star exposed inner in
    S.sep_laws ();
    I.write_atomic_inv mask r desired j;
    P.atomic_frame mask inner e q exposed;
    R.entails_refl pre;
    introduce forall v. S.implies (P.framed_post q exposed v) (P.prepend_post exposed q v)
    with R.entails_refl (P.prepend_post exposed q v);
    P.atomic_consequence mask (S.star inner exposed) pre e
      (P.framed_post q exposed) (P.prepend_post exposed q);
    P.atomic_invariant GS.empty i body inner e q;
    let protected = S.star (S.inv i body) inner in
    let post = P.constant_post #TUnit protected in
    R.entails_refl protected;
    introduce forall v. S.implies (P.prepend_post (S.inv i body) q v) (post v)
    with R.entails_refl (post v);
    P.atomic_consequence GS.empty protected protected e (P.prepend_post (S.inv i body) q) post;
    P.atomic_to_hoare protected e post

let nested_handle_write (r:PulseCore.Heap.core_ref) (desired:B.bit)
  (i:S.iref) (j:S.iref{not (j == i)})
  : Lemma (P.hoare
      (S.star (S.inv i (S.inv j (B.bit_cell r))) (S.later_credit 1))
      (Store (Val r) (Val desired))
      (P.constant_post (S.inv i (S.inv j (B.bit_cell r)))))
  = let body = S.inv j (B.bit_cell r) in
    let handle = S.inv i body in
    let mask = S.add_inv GS.empty i in
    let e = Store (Val r) (Val desired) in
    let credit = S.later_credit 1 in
    let pre = S.star (P.exposed body) credit in
    let inner_post = P.constant_post #TUnit body in
    let restored = P.constant_post #TUnit (P.exposed body) in
    let q = P.constant_post #TUnit S.emp in
    S.sep_laws ();
    R.exposed_inv j (B.bit_cell r);
    P.update_later_elim mask body;
    I.write_atomic_inv mask r desired j;
    R.entails_later body;
    introduce forall v. P.update mask mask (inner_post v) (restored v)
    with P.update_entails mask body (P.exposed body);
    P.atomic_updates mask mask pre body e inner_post restored;
    R.entails_refl pre;
    introduce forall v. S.implies (restored v) (P.prepend_post (P.exposed body) q v)
    with R.entails_refl (restored v);
    P.atomic_consequence mask pre pre e restored (P.prepend_post (P.exposed body) q);
    P.atomic_invariant GS.empty i body credit e q;
    R.entails_refl (S.star handle credit);
    introduce forall v. S.implies (P.prepend_post handle q v) (P.constant_post handle v)
    with R.entails_refl handle;
    P.atomic_consequence GS.empty (S.star handle credit) (S.star handle credit) e
      (P.prepend_post handle q) (P.constant_post handle);
    P.atomic_to_hoare (S.star handle credit) e (P.constant_post handle)

let nested_concurrent (r:PulseCore.Heap.core_ref)
  (i:S.iref) (j:S.iref{not (j == i)})
  : Lemma (P.hoare
      (S.star (S.inv i (S.inv j (B.bit_cell r)))
        (S.star (S.later_credit 1) (S.later_credit 1)))
      (I.concurrent r)
      (P.constant_post (S.inv i (S.inv j (B.bit_cell r)))))
  = let handle = S.inv i (S.inv j (B.bit_cell r)) in
    let credit = S.later_credit 1 in
    let owned = S.star handle credit in
    let child = Store (Val r) (Val 0) in
    let parent = Store (Val r) (Val 1) in
    S.sep_laws ();
    S.dup_inv_equiv i (S.inv j (B.bit_cell r));
    nested_handle_write r 0 i j;
    R.entails_refl owned;
    introduce forall (v:unit). S.implies handle S.emp with R.entails_emp handle;
    P.consequence owned owned child (P.constant_post handle) (P.constant_post S.emp);
    R.entails_refl owned;
    P.fork owned owned child (P.constant_post owned);
    nested_handle_write r 1 i j;
    P.sequence (S.star owned owned) owned (Fork child) parent (P.constant_post handle)
