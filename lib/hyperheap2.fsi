(*--build-config
    options:--admit_fsi Set --admit_fsi Map;
    other-files:set.fsi heap.fst map.fsi list.fst
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
module HyperHeap
open Map
open Heap
type rid
type t = Map.t rid heap
new_effect STATE = STATE_h t
val root : rid
type rref : rid -> Type -> Type
val as_ref      : #a:Type -> #id:rid -> r:rref id a -> GTot (ref a)
val ref_as_rref : #a:Type -> i:rid -> r:ref a -> GTot (rref i a)
val lemma_as_ref_inj: #a:Type -> #i:rid -> r:rref i a
    -> Lemma (requires (True))
             (ensures ((ref_as_rref i (as_ref r) = r)))
       [SMTPat (as_ref r)]

effect ST (a:Type) (pre:t -> Type) (post:t -> a -> t -> Type) =
       STATE a (fun 'p m0 -> pre m0 /\ (forall x m1. post m0 x m1 ==> 'p x m1))
               (fun 'p m0 ->  (forall x m1. pre m0 /\ post m0 x m1 ==> 'p x m1))

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
       (ensures (includes i j))
       [SMTPat (extends j i)]

val lemma_extends_disjoint: i:rid -> j:rid -> k:rid ->
   Lemma (requires (extends j i /\ extends k i /\ j<>k))
         (ensures (disjoint j k))
         [SMTPat (extends j i);
          SMTPat (extends k i)]
            
type fresh_region (i:rid) (m0:t) (m1:t) =
 (forall j. includes i j ==> not (Map.contains m0 j))
 /\ Map.contains m1 i

let sel (#a:Type) (#i:rid) (m:t) (r:rref i a) = Heap.sel (Map.sel m i) (as_ref r)
let upd (#a:Type) (#i:rid) (m:t) (r:rref i a) (v:a) = Map.upd m i (Heap.upd (Map.sel m i) (as_ref r) v)

val new_region: r0:rid -> ST rid
      (requires (fun m -> True))
      (ensures (fun (m0:t) (r1:rid) (m1:t) ->
                           extends r1 r0
                        /\ fresh_region r1 m0 m1
                        /\ m1=Map.upd m0 r1 Heap.emp))

val ralloc: #a:Type -> i:rid -> init:a -> ST (rref i a)
    (requires (fun m -> True))
    (ensures (fun m0 x m1 ->
                    Let (Map.sel m0 i) (fun region_i ->
                    not (Heap.contains region_i (as_ref x))
                    /\ m1=Map.upd m0 i (Heap.upd region_i (as_ref x) init))))

val op_Colon_Equals: #a:Type -> #i:rid -> r:rref i a -> v:a -> ST unit
  (requires (fun m -> True))
  (ensures (fun m0 _u m1 -> m1=Map.upd m0 i (Heap.upd (Map.sel m0 i) (as_ref r) v)))

val op_Bang:#a:Type -> #i:rid -> r:rref i a -> ST a
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m1=m0 /\ x=Heap.sel (Map.sel m0 i) (as_ref r)))

val get: unit -> ST t
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m0=x /\ m1=m0))

val mod_set : Set.set rid -> Tot (Set.set rid)
assume Mod_set_def: forall (x:rid) (s:Set.set rid). {:pattern Set.mem x (mod_set s)}
                    Set.mem x (mod_set s) <==> (exists (y:rid). Set.mem y s /\ includes y x)

opaque logic type modifies (s:Set.set rid) (m0:t) (m1:t) =
  Map.Equal m1 (Map.concat m1 (Map.restrict (Set.complement (mod_set s)) m0))

val lemma_modifies_trans: m1:t -> m2:t -> m3:t
                       -> s1:Set.set rid -> s2:Set.set rid
                       -> Lemma (requires (modifies s1 m1 m2 /\ modifies s2 m2 m3))
                                (ensures (modifies (Set.union s1 s2) m1 m3))

type contains_ref (#a:Type) (#i:rid) (r:rref i a) (m:t) =
    Map.contains m i /\ Heap.contains (Map.sel m i) (as_ref r)

type fresh_rref (#a:Type) (#i:rid) (r:rref i a) (m0:t) (m1:t) =
  not (Heap.contains (Map.sel m0 i) (as_ref r))
  /\  (Heap.contains (Map.sel m1 i) (as_ref r))

kind STPost (a:Type) = a -> t -> Type
kind STWP (a:Type) = STPost a -> t -> Type

sub_effect
  DIV   ~> STATE = fun (a:Type) (wp:PureWP a) (p:STPost a) (h:t) -> wp (fun a -> p a h)

  (*opaque type modifies1 (s:Set.set rid) (m0:t) (m1:t) =
    (forall (id:rid). Map.contains m0 id ==> Map.contains m1 id)
    /\ (forall (id:rid).//{:pattern (Map.sel m1 id)}
              Map.contains m0 id
              /\ (forall (mod:rid). Set.mem mod s ==> not (includes mod id))
              ==> Map.sel m1 id = Map.sel m0 id)*)
