(*
   Copyright 2019 Microsoft Research

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
module Steel.PCM.Heap
open FStar.Ghost
open Steel.PCM

/// Abstract type of heaps
val heap  : Type u#(a + 1)

/// A heap maps a reference to its associated value
val ref (a:Type u#a) (pcm:pcm a) : Type u#0

/// A predicate describing non-overlapping heaps
val disjoint (m0 m1:heap u#h) : prop

/// disjointness is symmetric
val disjoint_sym (m0 m1:heap u#h)
  : Lemma (disjoint m0 m1 <==> disjoint m1 m0)
          [SMTPat (disjoint m0 m1)]

/// disjoint heaps can be combined
val join (m0:heap u#h) (m1:heap u#h{disjoint m0 m1}) : heap u#h

val join_commutative (m0 m1:heap)
  : Lemma
    (requires
      disjoint m0 m1)
    (ensures
      (disjoint_sym m0 m1;
       join m0 m1 == join m1 m0))

/// disjointness distributes over join
val disjoint_join (m0 m1 m2:heap)
  : Lemma (disjoint m1 m2 /\
           disjoint m0 (join m1 m2) ==>
           disjoint m0 m1 /\
           disjoint m0 m2 /\
           disjoint (join m0 m1) m2 /\
           disjoint (join m0 m2) m1)

val join_associative (m0 m1 m2:heap)
  : Lemma
    (requires
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2))
    (ensures
      (disjoint_join m0 m1 m2;
       join m0 (join m1 m2) == join (join m0 m1) m2))

let heap_prop_is_affine (p:heap u#a -> prop) : prop =
  forall (h0 h1: heap u#a). p h0 /\ disjoint h0 h1 ==> p (join h0 h1)

let a_heap_prop : Type u#(a + 1) = p:(heap u#a -> prop) { heap_prop_is_affine p }

/// The type of heap assertions
[@@erasable]
val slprop : Type u#(a + 1)

/// interpreting heap assertions as heapory predicates
val interp (p:slprop u#a) (m:heap u#a) : prop

/// A common abbreviation: heaps validating p
let hheap (p:slprop u#a) = m:heap u#a {interp p m}

/// Equivalence relation on slprops is just
/// equivalence of their interpretations
let equiv (p1 p2:slprop) =
  forall m. interp p1 m <==> interp p2 m

/// All the standard connectives of separation logic
val emp : slprop u#a
val pts_to (#a:Type u#a) (#pcm:_) (r:ref a pcm) (v:a) : slprop u#a
val h_and (p1 p2:slprop u#a) : slprop u#a
val h_or  (p1 p2:slprop u#a) : slprop u#a
val star  (p1 p2:slprop u#a) : slprop u#a
val wand  (p1 p2:slprop u#a) : slprop u#a
val h_exists (#a:Type u#a) (f: (a -> slprop u#a)) : slprop u#a
val h_forall (#a:Type u#a) (f: (a -> slprop u#a)) : slprop u#a
val h_refine (p:slprop u#a) (r:a_heap_prop u#a) : slprop u#a

////////////////////////////////////////////////////////////////////////////////
//properties of equiv
////////////////////////////////////////////////////////////////////////////////

val equiv_symmetric (p1 p2:slprop)
  : squash (p1 `equiv` p2 ==> p2 `equiv` p1)

val equiv_extensional_on_star (p1 p2 p3:slprop)
  : squash (p1 `equiv` p2 ==> (p1 `star` p3) `equiv` (p2 `star` p3))

(** Properties of emp *)
val emp_unit (p:slprop)
  : Lemma (p `equiv` (p `star` emp))

////////////////////////////////////////////////////////////////////////////////
// pts_to and abbreviations
//////////////////////////////////////////////////////////////////////////////////////////
let ptr #a #pcm (r:ref a pcm) =
    h_exists (pts_to r)

val pts_to_compatible (#a:Type u#a)
                      (#pcm:_)
                      (x:ref a pcm)
                      (v0 v1:a)
                      (m:heap u#a)
  : Lemma
    (requires
      interp (pts_to x v0 `star` pts_to x v1) m)
    (ensures
      composable pcm v0 v1 /\
      interp (pts_to x (op pcm v0 v1)) m)

////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////

val intro_star (p q:slprop) (mp:hheap p) (mq:hheap q)
  : Lemma
    (requires
      disjoint mp mq)
    (ensures
      interp (p `star` q) (join mp mq))

val star_commutative (p1 p2:slprop)
  : Lemma ((p1 `star` p2) `equiv` (p2 `star` p1))

val star_associative (p1 p2 p3:slprop)
  : Lemma ((p1 `star` (p2 `star` p3))
           `equiv`
           ((p1 `star` p2) `star` p3))

val star_congruence (p1 p2 p3 p4:slprop)
  : Lemma (requires p1 `equiv` p3 /\ p2 `equiv` p4)
          (ensures (p1 `star` p2) `equiv` (p3 `star` p4))

val affine_star (p q:slprop) (m:heap)
  : Lemma ((interp (p `star` q) m ==> interp p m /\ interp q m))

////////////////////////////////////////////////////////////////////////////////
// refine
////////////////////////////////////////////////////////////////////////////////

val refine_interp (p:slprop u#a) (q:a_heap_prop u#a) (h:heap u#a)
    : Lemma (interp p h /\ q h <==> interp (h_refine p q) h)

val refine_equiv (p0 p1:slprop u#a) (q0 q1:a_heap_prop u#a)
    : Lemma (p0 `equiv` p1 /\ (forall h. q0 h <==> q1 h) <==>
             equiv (h_refine p0 q0) (h_refine p1 q1))

////////////////////////////////////////////////////////////////////////////////
// Actions:
////////////////////////////////////////////////////////////////////////////////
val free_above_addr (h:heap u#a) (a:nat) : prop

(** A heap predicate that depends only on fp *)
let hprop (fp:slprop u#a) =
  q:(heap u#a -> prop){
    forall (m0:heap{interp fp m0}) (m1:heap{disjoint m0 m1}).
      q m0 <==> q (join m0 m1)}

let pre_action (fp:slprop) (a:Type) (fp':a -> slprop) =
  hheap fp -> (x:a & hheap (fp' x))

let is_frame_preserving #a #fp #fp' (f:pre_action fp a fp') =
   forall frame (h0:hheap (fp `star` frame)).
     (affine_star fp frame h0;
      let (| x, h1 |) = f h0 in
      interp (fp' x `star` frame) h1 /\
      (forall ctr. h0 `free_above_addr` ctr <==> h1 `free_above_addr` ctr) /\
      (forall (hp:hprop frame). hp h0 == hp h1))


let action (fp:slprop) (a:Type) (fp':a -> slprop) =
  f:pre_action fp a fp'{ is_frame_preserving f }

let frame_related_heaps (h0 h1:heap) (fp0 fp1 frame:slprop) =
  interp (fp0 `star` frame) h0 /\
  interp (fp1 `star` frame) h1 /\
  (forall ctr. h0 `free_above_addr` ctr <==> h1 `free_above_addr` ctr) /\
  (forall (hp:hprop frame). hp h0 == hp h1)

let action_framing #a #fp #fp' ($f:action fp a fp')
                         (frame:slprop) (h0:hheap (fp `star` frame))
  : Lemma (affine_star fp frame h0;
           let (| x, h1 |) = f h0 in
           frame_related_heaps h0 h1 fp (fp' x) frame)
  = affine_star fp frame h0;
    emp_unit fp

(** Reading *)
val sel (#a:_) (#pcm:_) (r:ref a pcm) (m:hheap (ptr r))
  : a

/// sel respect pts_to
val sel_lemma (#a:_) (#pcm:_) (r:ref a pcm) (m:hheap (ptr r))
  : Lemma (interp (pts_to r (sel r m)) m)

val sel_action (#a:_) (#pcm:_) (r:ref a pcm) (v0:erased a)
  : action (pts_to r v0) (v:a{compatible pcm v0 v}) (fun _ -> pts_to r v0)

(** Writing *)
/// updating a ref cell from v0 to v1
/// must be compatible with other views of the same cell
val upd_action (#a:_) (#pcm:_) (r:ref a pcm)
               (v0:FStar.Ghost.erased a)
               (v1:a {Steel.PCM.frame_preserving pcm v0 v1})
  : action (pts_to r v0) unit (fun _ -> pts_to r v1)

(** Allocating, pseudo action *)
val extend (#a:_) (#pcm:_) (x:a) (addr:nat)
           (h:heap{h `free_above_addr` addr})
  : (r:ref a pcm & h':heap{(forall f. interp f h ==> interp f h') /\
                           interp (pts_to r x) h' /\
                           h' `free_above_addr` (addr + 1)})

val interp_depends_only_on (hp:slprop u#a)
    : Lemma
      (forall (m0:hheap hp) (m1:heap u#a{disjoint m0 m1}).
        interp hp m0 <==> interp hp (join m0 m1))

val h_exists_cong (#a:Type) (p q : a -> slprop)
    : Lemma
      (requires (forall x. p x `equiv` q x))
      (ensures (h_exists p `equiv` h_exists q))
