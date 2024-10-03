(*
   Copyright 2008-2014 Nikhil Swamy, Aseem Rastogi, and Microsoft Research

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
module FStar.Monotonic.HyperHeap

module Set = FStar.Set
module Map = FStar.Map

open FStar.Monotonic.Heap
open FStar.Ghost

(*
 * This module provides the map view of the memory and associated functions and lemmas
 * The intention of this module is for it to be included in HyperStack
 * Clients should not open/know about HyperHeap, they should work only with HyperStack
 *)

(*
 * AR: mark it erasable temporarily until CMI comes in
 *)
[@@erasable]
val rid :eqtype

val reveal (r:rid) :GTot (list (int & int))

let rid_last_component (r:rid) :GTot int
  = let open FStar.List.Tot.Base in
    let r = reveal r in
    if length r = 0 then 0
    else snd (hd r)

val color (x:rid) :GTot int

val rid_freeable (x:rid) : GTot bool

type hmap = Map.t rid heap

val root : r:rid{color r == 0 /\ not (rid_freeable r)}

val root_last_component (_:unit) : Lemma (rid_last_component root == 0)

let root_has_color_zero (u:unit) :Lemma (color root == 0) = ()

val root_is_not_freeable (_:unit) : Lemma (not (rid_freeable root))

private val rid_length (r:rid) :GTot nat

private val rid_tail (r:rid{rid_length r > 0}) :rid

val includes (r1:rid) (r2:rid) :GTot bool (decreases (reveal r2))

let disjoint (i:rid) (j:rid) :GTot bool = not (includes i j) && not (includes j i)

val lemma_disjoint_includes (i:rid) (j:rid) (k:rid)
  :Lemma (requires  (disjoint i j /\ includes j k))
         (ensures   (disjoint i k))
         (decreases (List.Tot.Base.length (reveal k)))
         [SMTPat (disjoint i j); SMTPat (includes j k)]

val extends (i:rid) (j:rid) :GTot bool

val parent (r:rid{r =!= root}) :rid

val lemma_includes_refl (i:rid)
  :Lemma (includes i i)
         [SMTPat (includes i i)]

val lemma_extends_includes (i:rid) (j:rid)
  :Lemma (requires (extends j i))
         (ensures  (includes i j /\ not(includes j i)))
         [SMTPat (extends j i)]

val lemma_includes_anti_symmetric (i:rid) (j:rid)
  :Lemma (requires (includes i j /\ i =!= j))
         (ensures  (not (includes j i)))
         [SMTPat (includes i j)]

val lemma_extends_disjoint (i:rid) (j:rid) (k:rid)
  :Lemma (requires (extends j i /\ extends k i /\ j =!= k))
         (ensures  (disjoint j k))

val lemma_extends_parent (i:rid{i =!= root})
  :Lemma (extends i (parent i))
         [SMTPat (parent i)]

val lemma_extends_not_root (i:rid) (j:rid{extends j i})
  :Lemma (j =!= root)
         [SMTPat (extends j i)]

val lemma_extends_only_parent (i:rid) (j:rid{extends j i})
  :Lemma (i == parent j)
         [SMTPat (extends j i)]

val mod_set (s:Set.set rid) :(Set.set rid)
assume Mod_set_def: forall (x:rid) (s:Set.set rid). {:pattern Set.mem x (mod_set s)}
                    Set.mem x (mod_set s) <==> (exists (y:rid). Set.mem y s /\ includes y x)

let modifies (s:Set.set rid) (m0:hmap) (m1:hmap) =
  Map.equal m1 (Map.concat m1 (Map.restrict (Set.complement (mod_set s)) m0)) /\
  Set.subset (Map.domain m0) (Map.domain m1)

let modifies_just (s:Set.set rid) (m0:hmap) (m1:hmap) =
  Map.equal m1 (Map.concat m1 (Map.restrict (Set.complement s) m0)) /\
  Set.subset (Map.domain m0) (Map.domain m1)

let modifies_one (r:rid) (m0:hmap) (m1:hmap) = modifies_just (Set.singleton r) m0 m1

let equal_on (s:Set.set rid) (m0:hmap) (m1:hmap) =
 (forall (r:rid). {:pattern (Map.contains m0 r)} (Set.mem r (mod_set s) /\ Map.contains m0 r) ==> Map.contains m1 r) /\
 Map.equal m1 (Map.concat m1 (Map.restrict (mod_set s) m0))

let lemma_modifies_just_trans (m1:hmap) (m2:hmap) (m3:hmap)
  (s1:Set.set rid) (s2:Set.set rid)
  :Lemma (requires (modifies_just s1 m1 m2 /\ modifies_just s2 m2 m3))
         (ensures  (modifies_just (Set.union s1 s2) m1 m3))
  = ()

let lemma_modifies_trans (m1:hmap) (m2:hmap) (m3:hmap)
  (s1:Set.set rid) (s2:Set.set rid)
  :Lemma (requires (modifies s1 m1 m2 /\ modifies s2 m2 m3))
         (ensures  (modifies (Set.union s1 s2) m1 m3))
  = ()

val lemma_includes_trans (i:rid) (j:rid) (k:rid)
  :Lemma (requires  (includes i j /\ includes j k))
         (ensures   (includes i k))
         (decreases (reveal k))
         [SMTPat (includes i j); SMTPat (includes j k)]

val lemma_modset (i:rid) (j:rid)
  :Lemma (requires (includes j i))
         (ensures  (Set.subset (mod_set (Set.singleton i)) (mod_set (Set.singleton j))))

val lemma_modifies_includes (m1:hmap) (m2:hmap) (i:rid) (j:rid)
  :Lemma (requires (modifies (Set.singleton i) m1 m2 /\ includes j i))
         (ensures  (modifies (Set.singleton j) m1 m2))

val lemma_modifies_includes2 (m1:hmap) (m2:hmap) (s1:Set.set rid) (s2:Set.set rid)
  :Lemma (requires (modifies s1 m1 m2 /\ (forall x.  Set.mem x s1 ==> (exists y. Set.mem y s2 /\ includes y x))))
         (ensures  (modifies s2 m1 m2))

val lemma_disjoint_parents (pr:rid) (r:rid) (ps:rid) (s:rid)
  :Lemma (requires (r `extends` pr /\ s `extends` ps /\ disjoint pr ps))
         (ensures  (disjoint r s))
         [SMTPat (extends r pr); SMTPat (extends s ps); SMTPat (disjoint pr ps)]

val lemma_include_cons (i:rid) (j:rid)
  :Lemma (requires (i =!= j /\ includes i j))
         (ensures  (j =!= root))

let disjoint_regions (s1:Set.set rid) (s2:Set.set rid) =
     forall x y. {:pattern (Set.mem x s1); (Set.mem y s2)} (Set.mem x s1 /\ Set.mem y s2) ==> disjoint x y

val extends_parent (tip:rid{tip =!= root}) (r:rid)
  :Lemma (extends r (parent tip) /\ r =!= tip ==> disjoint r tip \/ extends r tip)
         [SMTPat (extends r (parent tip))]

val includes_child (tip:rid{tip =!= root}) (r:rid)
  :Lemma (includes r tip ==> r == tip \/ includes r (parent tip))
         [SMTPat (includes r (parent tip))]

val root_is_root (s:rid)
  :Lemma (requires (includes s root))
         (ensures  (s == root))
         [SMTPat (includes s root)]

unfold
let extend_post (r:rid) (n:int) (c:int) (freeable:bool) : pure_post rid =
  fun s ->
  s `extends` r /\
  Cons? (reveal s) /\
  Cons?.hd (reveal s) == (c, n) /\
  color s == c /\
  rid_freeable s == freeable
  
val extend (r:rid) (n:int) (c:int)
: Pure rid (requires True) (extend_post r n c (rid_freeable r))

val extend_monochrome_freeable (r:rid) (n:int) (freeable:bool)
: Pure rid (requires True) (extend_post r n (color r) freeable)

val extend_monochrome (r:rid) (n:int)
: Pure rid (requires True) (extend_post r n (color r) (rid_freeable r))
