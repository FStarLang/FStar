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
module Pulse.Extrinsic.InvariantExamples

(** Mutable invariant clients over an existential bit cell.
    write_atomic_inv opens one invariant around one store, changes its bit
    witness, and closes it. read_inv proves a bit result without retaining
    ownership of the body. Concurrent writers share only invariant handles.

    concurrent_readback returns 0 or 1, not necessarily the parent's value:
    fork does not join. concurrent_from_owned allocates the logical invariant
    from ordinary cell ownership. These proofs use the general invariant rule,
    never native actions or scheduler traces. *)

open Pulse.Extrinsic.HeapLang
open Pulse.Extrinsic.HeapLang.Notation
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module B = Pulse.Extrinsic.ExamplePredicates
module R = Pulse.Extrinsic.Rules
module S = PulseCore.IndirectionTheorySep
module GS = Pulse.Lib.GhostSet

let write_atomic_inv (outer:S.inames) (r:PulseCore.Heap.core_ref) (desired:B.bit)
  (i:S.iref{not (S.mem_inv outer i)})
  : Lemma (P.atomic outer (S.inv i (B.bit_cell r)) (Store (Val r) (Val desired))
      (P.constant_post (S.inv i (B.bit_cell r))))
  = let body = B.bit_cell r in
    let handle = S.inv i body in
    let e = Store (Val r) (Val desired) in
    let mask = S.add_inv outer i in
    let q = P.constant_post #TUnit S.emp in
    let restored = P.prepend_post (P.exposed body) q in
    S.sep_laws ();
    B.bit_cell_unfold r;
    B.bit_cell_intro r desired;
    B.bit_cell_exposed r;
    R.entails_trans (C.points_to r desired) body (P.exposed body);
    introduce forall (old:B.bit). P.atomic mask (B.bit_point r old) e restored
    with (
      P.atomic_store mask r old desired;
      R.entails_refl (C.points_to r old);
      P.atomic_consequence mask (C.points_to r old) (C.points_to r old) e
        (P.constant_post (C.points_to r desired)) restored
    );
    P.atomic_exists mask (B.bit_point r) e restored;
    introduce forall v. S.implies (restored v) (restored v) with R.entails_refl (restored v);
    P.atomic_consequence mask body (S.star (P.exposed body) S.emp) e restored restored;
    P.atomic_invariant outer i body S.emp e q;
    R.entails_refl handle;
    P.atomic_consequence outer handle handle e
      (P.prepend_post handle q) (P.constant_post handle)

let write_inv (r:PulseCore.Heap.core_ref) (desired:B.bit) (i:S.iref)
  : Lemma (P.hoare (S.inv i (B.bit_cell r)) (Store (Val r) (Val desired))
      (P.constant_post (S.inv i (B.bit_cell r))))
  = let handle = S.inv i (B.bit_cell r) in
    let e = Store (Val r) (Val desired) in
    write_atomic_inv GS.empty r desired i;
    P.atomic_to_hoare handle e (P.constant_post handle)

let bit_result (v:int) = S.pure (v == 0 \/ v == 1)

let read_inv (r:PulseCore.Heap.core_ref) (i:S.iref)
  : Lemma (P.hoare (S.inv i (B.bit_cell r)) (Load (Val r))
      (P.prepend_post (S.inv i (B.bit_cell r)) bit_result))
  = let body = B.bit_cell r in
    let e = Load (Val r) in
    let mask = S.add_inv GS.empty i in
    let restored = P.prepend_post (P.exposed body) bit_result in
    S.sep_laws ();
    B.bit_cell_unfold r;
    B.bit_cell_exposed r;
    introduce forall (old:B.bit). P.atomic mask (B.bit_point r old) e restored
    with (
      P.atomic_load mask r old;
      B.bit_cell_intro r old;
      R.entails_trans (C.points_to r old) body (P.exposed body);
      introduce forall v. S.implies (P.read_post r old v) (restored v)
      with (
        R.entails_pure (v == old) (v == 0 \/ v == 1);
        R.entails_star (C.points_to r old) (P.exposed body)
          (S.pure (v == old)) (bit_result v)
      );
      R.entails_refl (C.points_to r old);
      P.atomic_consequence mask (C.points_to r old) (C.points_to r old) e
        (P.read_post r old) restored
    );
    P.atomic_exists mask (B.bit_point r) e restored;
    introduce forall v. S.implies (restored v) (restored v) with R.entails_refl (restored v);
    P.atomic_consequence mask body (S.star (P.exposed body) S.emp) e restored restored;
    P.atomic_invariant GS.empty i body S.emp e bit_result;
    P.atomic_to_hoare (S.inv i body) e (P.prepend_post (S.inv i body) bit_result)

let concurrent (r:PulseCore.Heap.core_ref) : expr [] TUnit =
  fork (store (ref_ r) (int_ 0)) >> store (ref_ r) (int_ 1)

let concurrent_correct (r:PulseCore.Heap.core_ref) (i:S.iref)
  : Lemma (P.hoare (S.inv i (B.bit_cell r)) (concurrent r)
      (P.constant_post (S.inv i (B.bit_cell r))))
  = let p = S.inv i (B.bit_cell r) in
    let child = Store (Val r) (Val 0) in
    let parent = Store (Val r) (Val 1) in
    S.sep_laws ();
    S.dup_inv_equiv i (B.bit_cell r);
    R.entails_refl p;
    write_inv r 0 i;
    introduce forall (v:unit). S.implies p S.emp with R.entails_emp p;
    P.consequence p p child (P.constant_post p) (P.constant_post S.emp);
    P.fork p p child (P.constant_post p);
    write_inv r 1 i;
    P.sequence p p (Fork child) parent (P.constant_post p)

let concurrent_readback (r:PulseCore.Heap.core_ref) : expr [] TInt =
  concurrent r >> load (ref_ r)

let concurrent_readback_correct (r:PulseCore.Heap.core_ref) (i:S.iref)
  : Lemma (P.hoare (S.inv i (B.bit_cell r)) (concurrent_readback r)
      (P.prepend_post (S.inv i (B.bit_cell r)) bit_result))
  = let p = S.inv i (B.bit_cell r) in
    concurrent_correct r i;
    read_inv r i;
    P.sequence p p (concurrent r) (Load (Val r)) (P.prepend_post p bit_result)

let concurrent_from_owned (r:PulseCore.Heap.core_ref) (initial:B.bit)
  : Lemma (P.hoare (C.points_to r initial) (concurrent_readback r) bit_result)
  = let body = B.bit_cell r in
    let e = concurrent_readback r in
    S.sep_laws ();
    P.allocate_invariant body S.emp e bit_result (fun i ->
      let p = S.inv i body in
      concurrent_readback_correct r i;
      R.entails_refl p;
      introduce forall v. S.implies (P.prepend_post p bit_result v) (bit_result v)
      with (
        R.entails_emp p;
        R.entails_refl (bit_result v);
        R.entails_star p S.emp (bit_result v) (bit_result v)
      );
      P.consequence p p e (P.prepend_post p bit_result) bit_result);
    B.bit_cell_intro r initial;
    introduce forall v. S.implies (bit_result v) (bit_result v)
    with R.entails_refl (bit_result v);
    P.consequence body (C.points_to r initial) e bit_result bit_result
