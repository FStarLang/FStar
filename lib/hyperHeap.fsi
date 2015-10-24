(*--build-config
    options:--admit_fsi Set --admit_fsi Map;
    other-files:set.fsi heap.fst map.fsi listTot.fst
 --*)
(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStar.HyperHeap
open FStar.Map
open FStar.Heap
type rid
type t = Map.t rid heap
val root : rid

type rref : rid -> Type -> Type
val as_ref      : #a:Type -> #id:rid -> r:rref id a -> GTot (ref a)
val ref_as_rref : #a:Type -> i:rid -> r:ref a -> GTot (rref i a)
type proj_type (#a:Type) (#id:rid) (r:rref id a) = a

val lemma_as_ref_inj: #a:Type -> #i:rid -> r:rref i a
    -> Lemma (requires (True))
             (ensures ((ref_as_rref i (as_ref r) = r)))
       [SMTPat (as_ref r)]
val lemma_proj_typ_inj: #a:Type -> #i:rid -> r:rref i a
    -> Lemma (requires True)
             (ensures ((rref i (proj_type r) == rref i a)))
             [SMTPat (as_ref r)]

val includes : rid -> rid -> Tot bool
val extends  : rid -> rid -> Tot bool
let disjoint i j = not (includes i j) && not (includes j i)

val lemma_includes_refl: i:rid
                      -> Lemma (requires (True))
                               (ensures (includes i i))
                               [SMTPat (includes i i)]

val lemma_disjoint_includes: i:rid -> j:rid -> k:rid ->
  Lemma (requires (disjoint i j /\ includes j k))
        (ensures (disjoint i k))
        [SMTPat (disjoint i j);
         SMTPat (includes j k)]

val lemma_extends_includes: i:rid -> j:rid ->
 Lemma (requires (extends j i))
       (ensures (includes i j /\ not(includes j i)))
       [SMTPat (extends j i)]

val lemma_extends_disjoint: i:rid -> j:rid -> k:rid ->
   Lemma (requires (extends j i /\ extends k i /\ j<>k))
         (ensures (disjoint j k))
         [SMTPat (extends j i);
          SMTPat (extends k i)]

val lemma_includes_trans: i:rid -> j:rid -> k:rid
                        -> Lemma (requires (includes i j /\ includes j k))
                                 (ensures (includes i k))
                                 [SMTPat (includes i j);
                                  SMTPat (includes j k)]

val lemma_disjoint_parents: pr:rid -> r:rid -> ps:rid -> s:rid -> Lemma
  (requires (extends r pr /\ extends s ps /\ disjoint pr ps))
  (ensures (disjoint r s))
  [SMTPat (extends r pr); SMTPat (extends s ps); SMTPat (disjoint pr ps)]

type fresh_region (i:rid) (m0:t) (m1:t) =
 (forall j. includes i j ==> not (Map.contains m0 j))
 /\ Map.contains m1 i

let sel (#a:Type) (#i:rid) (m:t) (r:rref i a) = Heap.sel (Map.sel m i) (as_ref r)
let upd (#a:Type) (#i:rid) (m:t) (r:rref i a) (v:a) = Map.upd m i (Heap.upd (Map.sel m i) (as_ref r) v)

val mod_set : Set.set rid -> Tot (Set.set rid)
assume Mod_set_def: forall (x:rid) (s:Set.set rid). {:pattern Set.mem x (mod_set s)}
                    Set.mem x (mod_set s) <==> (exists (y:rid). Set.mem y s /\ includes y x)

opaque logic type modifies (s:Set.set rid) (m0:t) (m1:t) =
  Map.Equal m1 (Map.concat m1 (Map.restrict (Set.complement (mod_set s)) m0))

opaque logic type modifies_one (r:rid) (m0:t) (m1:t) =
  Map.Equal m1 (Map.concat m1 (Map.restrict (Set.complement (Set.singleton r)) m0))

opaque logic type equal_on (s:Set.set rid) (m0:t) (m1:t) =
 (forall (r:rid). {:pattern (Map.contains m0 r)} (Set.mem r (mod_set s) /\ Map.contains m0 r) ==> Map.contains m1 r)
 /\ Map.Equal m0 (Map.concat m0 (Map.restrict (mod_set s) m1))

val lemma_modifies_trans: m1:t -> m2:t -> m3:t
                       -> s1:Set.set rid -> s2:Set.set rid
                       -> Lemma (requires (modifies s1 m1 m2 /\ modifies s2 m2 m3))
                                (ensures (modifies (Set.union s1 s2) m1 m3))

type contains_ref (#a:Type) (#i:rid) (r:rref i a) (m:t) =
    Map.contains m i /\ Heap.contains (Map.sel m i) (as_ref r)

type fresh_rref (#a:Type) (#i:rid) (r:rref i a) (m0:t) (m1:t) =
  not (Heap.contains (Map.sel m0 i) (as_ref r))
  /\  (Heap.contains (Map.sel m1 i) (as_ref r))

type modifies_rref (r:rid) (s:Set.set aref) h0 h1 = Heap.modifies s (Map.sel h0 r) (Map.sel h1 r)
