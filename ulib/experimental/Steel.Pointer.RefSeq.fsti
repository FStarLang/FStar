(*
   Copyright 2021 Microsoft Research

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

module Steel.Pointer.RefSeq
open Steel.Memory
open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference

[@@erasable]
noeq
type gpair (a b: Type) = | GPair: (fst: a) -> (snd: b) -> gpair a b

let array1 (a: Type) = Seq.seq (ref a)
let array2 (a: Type) = Ghost.erased (array1 a)

val hp_varray2
  (#a: Type0)
  (r: array2 a)
  (p: perm)
: Tot (slprop u#1)

val sel_varray2
  (#a: Type0)
  (r: array2 a)
  (p: perm)
: Tot (selector (Seq.lseq a (Seq.length r)) (hp_varray2 r p))

[@@ __steel_reduce__]
let varray2' (#a: Type0) (r: array2 a) (p: perm) : vprop' =
  {hp = hp_varray2 r p;
   t = Seq.lseq a (Seq.length r);
   sel = sel_varray2 r p}

[@@ __steel_reduce__]
let varray2 r p = VUnit (varray2' r p)

val vappend
  (#opened: _)
  (#t: Type)
  (a1 a2: array2 t)
  (p: perm)
: SteelGhost (array2 t) opened
    (varray2 a1 p `star` varray2 a2 p)
    (fun r -> varray2 r p)
    (fun _ -> True)
    (fun h r h' ->
      h' (varray2 r p) == Seq.append (h (varray2 a1 p)) (h (varray2 a2 p)) /\
      Ghost.reveal r == Seq.append a1 a2
    )

val vsplit
  (#opened: _)
  (#t: Type)
  (p: perm)
  (a: array2 t)
  (i: nat)
: SteelGhost (array2 t `gpair` array2 t) opened
    (varray2 a p)
    (fun res -> varray2 (GPair?.fst res) p `star` varray2 (GPair?.snd res) p)
    (fun _ -> i <= Seq.length a)
    (fun h res h' ->
      let s = h (varray2 a p) in
      i <= Seq.length a /\
      GPair?.fst res `Seq.equal` Seq.slice a 0 i /\
      GPair?.snd res `Seq.equal` Seq.slice a i (Seq.length a) /\
      (a <: Seq.seq (ref t)) == Seq.append (GPair?.fst res) (GPair?.snd res) /\
      h' (varray2 (GPair?.fst res) p) == Seq.slice s 0 i /\
      h' (varray2 (GPair?.snd res) p) `Seq.equal` Seq.slice s i (Seq.length a) /\
      s == Seq.append (h' (varray2 (GPair?.fst res) p)) (h' (varray2 (GPair?.snd res) p))
    )

[@@erasable]
noeq
type ith_t
  (t: Type)
= {
  ith_lhs: array2 t;
  ith_item: ref t;
  ith_rhs: array2 t;
}

let seq_index_append_cons
  (#t: Type)
  (i: nat)
  (a: Seq.seq t) (x: t) (b: Seq.seq t)
: Lemma
  (requires (Seq.length a == i))
  (ensures (Seq.index (Seq.append a (Seq.cons x b)) i == x))
= ()

let seq_upd_append_cons
  (#t: Type)
  (i: nat)
  (y: t)
  (a: Seq.seq t) (x: t) (b: Seq.seq t)
: Lemma
  (Seq.length a == i ==> Seq.upd (Seq.append a (Seq.cons x b)) i y == Seq.append a (Seq.cons y b))
=
  assert (Seq.length a == i ==> Seq.upd (Seq.append a (Seq.cons x b)) i y `Seq.equal` Seq.append a (Seq.cons y b))

val unpack_ith
  (#opened: _)
  (#t: Type)
  (p: perm)
  (a: array2 t)
  (i: nat)
: SteelGhost (ith_t t) opened
    (varray2 a p)
    (fun res -> varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p)
    (fun _ -> i < Seq.length a)
    (fun h res h' ->
      i < Seq.length a /\
      Ghost.reveal a == Seq.append res.ith_lhs (Seq.cons (res.ith_item) res.ith_rhs) /\
      can_be_split (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p) (varray2 res.ith_lhs p) /\
      can_be_split (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p) (vptrp res.ith_item p) /\
      can_be_split (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p) (varray2 res.ith_lhs p) /\
      h (varray2 a p) == Seq.append (h' (varray2 res.ith_lhs p)) (Seq.cons (h' (vptrp res.ith_item p)) (h' (varray2 res.ith_rhs p))) /\
      Seq.length res.ith_lhs == i
    )

val pack_ith
  (#opened: _)
  (#t: Type)
  (p: perm)
  (res: ith_t t)
  (a: array2 t)
: SteelGhost unit opened
    (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p)
    (fun _ -> varray2 a p)
    (fun _ ->
      Ghost.reveal a == Seq.append res.ith_lhs (Seq.cons (res.ith_item) res.ith_rhs)
    )
    (fun h _ h' ->
      let i = Seq.length res.ith_lhs in
      can_be_split (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p) (varray2 res.ith_lhs p) /\
      can_be_split (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p) (vptrp res.ith_item p) /\
      h' (varray2 a p) == Seq.append (h (varray2 res.ith_lhs p)) (Seq.cons (h (vptrp res.ith_item p)) (h (varray2 res.ith_rhs p)))
    )

val valloc
  (#t: Type)
  (i: nat)
  (x: t)
: Steel (array1 t)
    emp
    (fun res -> varray2 res full_perm)
    (fun _ -> True)
    (fun _ res h' ->
      Seq.length res == i /\
      h' (varray2 res full_perm) == Seq.create i x
    )

val vshare
  (#opened: _)
  (#t: Type)
  (a: array2 t)
  (p: perm)
: SteelGhost perm opened
    (varray2 a p)
    (fun res -> varray2 a res `star` varray2 a res)
    (fun _ -> True)
    (fun h res h' ->
      h' (varray2 a res) `Seq.equal` h (varray2 a p) /\
      res == half_perm p
    )

val vgather
  (#opened: _)
  (#t: Type)
  (a: array2 t)
  (p1 p2: perm)
: SteelGhost perm opened
    (varray2 a p1 `star` varray2 a p2)
    (fun res -> varray2 a res)
    (fun _ -> True)
    (fun h res h' ->
      h' (varray2 a res) `Seq.equal` h (varray2 a p1) /\
      h' (varray2 a res) `Seq.equal` h (varray2 a p2) /\
      res == p1 `sum_perm` p2
    )

val vfree
  (#t: Type)
  (x: array1 t)
: SteelT unit
    (varray2 x full_perm)
    (fun _ -> emp)
