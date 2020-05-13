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
module Steel.PCM.Memory
open FStar.Ghost
open Steel.PCM

/// Abstract type of memories
val mem  : Type u#(a + 1)
val core_mem (m:mem u#a) : mem u#a

/// A predicate describing non-overlapping memories
val disjoint (m0 m1:mem u#h) : prop

/// disjointness is symmetric
val disjoint_sym (m0 m1:mem u#h)
  : Lemma (disjoint m0 m1 <==> disjoint m1 m0)
          [SMTPat (disjoint m0 m1)]

/// disjoint memories can be combined
val join (m0:mem u#h) (m1:mem u#h{disjoint m0 m1}) : mem u#h

val join_commutative (m0 m1:mem)
  : Lemma
    (requires
      disjoint m0 m1)
    (ensures
      (disjoint_sym m0 m1;
       join m0 m1 == join m1 m0))

/// disjointness distributes over join
val disjoint_join (m0 m1 m2:mem)
  : Lemma (disjoint m1 m2 /\
           disjoint m0 (join m1 m2) ==>
           disjoint m0 m1 /\
           disjoint m0 m2 /\
           disjoint (join m0 m1) m2 /\
           disjoint (join m0 m2) m1)

val join_associative (m0 m1 m2:mem)
  : Lemma
    (requires
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2))
    (ensures
      (disjoint_join m0 m1 m2;
       join m0 (join m1 m2) == join (join m0 m1) m2))

/// The type of mem assertions
//[@@erasable] I would like this to be abstract, but I can't define an abstract abbreviation of an erasable type and have it be erasable too. Need to fix that after which this interface should not expose its dependence on Heap
let slprop = Steel.PCM.Heap.slprop

/// interpreting mem assertions as memory predicates
val interp (p:slprop u#a) (m:mem u#a) : prop

/// A common abbreviation: memories validating p
let hmem (p:slprop u#a) = m:mem u#a {interp p m}

/// Equivalence relation on slprops is just
/// equivalence of their interpretations
let equiv (p1 p2:slprop) =
  forall m. interp p1 m <==> interp p2 m

/// A heap maps a reference to its associated value
val ref (a:Type u#a) (pcm:pcm a) : Type u#0

/// All the standard connectives of separation logic
val emp : slprop u#a
val pts_to (#a:Type u#a) (#pcm:_) (r:ref a pcm) (v:a) : slprop u#a
val h_and (p1 p2:slprop u#a) : slprop u#a
val h_or  (p1 p2:slprop u#a) : slprop u#a
val star  (p1 p2:slprop u#a) : slprop u#a
val wand  (p1 p2:slprop u#a) : slprop u#a
val h_exists (#a:Type u#a) (f: (a -> slprop u#a)) : slprop u#a
val h_forall (#a:Type u#a) (f: (a -> slprop u#a)) : slprop u#a

////////////////////////////////////////////////////////////////////////////////
//properties of equiv
////////////////////////////////////////////////////////////////////////////////

val equiv_symmetric (p1 p2:slprop)
  : squash (p1 `equiv` p2 ==> p2 `equiv` p1)

val equiv_extensional_on_star (p1 p2 p3:slprop)
  : squash (p1 `equiv` p2 ==> (p1 `star` p3) `equiv` (p2 `star` p3))


////////////////////////////////////////////////////////////////////////////////
// pts_to and abbreviations
////////////////////////////////////////////////////////////////////////////////
let ptr #a #pcm (r:ref a pcm) =
    h_exists (pts_to r)

val pts_to_compatible (#a:Type u#a)
                      (#pcm:_)
                      (x:ref a pcm)
                      (v0 v1:a)
                      (m:mem u#a)
  : Lemma
    (requires
      interp (pts_to x v0 `star` pts_to x v1) m)
    (ensures
      composable pcm v0 v1 /\
      interp (pts_to x (op pcm v0 v1)) m)

////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////

val intro_star (p q:slprop) (mp:hmem p) (mq:hmem q)
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

val affine_star (p q:slprop) (m:mem)
  : Lemma ((interp (p `star` q) m ==> interp p m /\ interp q m))

////////////////////////////////////////////////////////////////////////////////
// Memory invariants
////////////////////////////////////////////////////////////////////////////////
val lock_addr : eqtype
module S = FStar.Set

val locks_invariant (e:S.set lock_addr) (m:mem u#a) : slprop u#a

let hmem_with_inv' (e:S.set lock_addr) (fp:slprop u#a) =
  m:mem{interp (fp `star` locks_invariant e m) m}

let hmem_with_inv (fp:slprop u#a) =
  m:mem u#a{interp (fp `star` locks_invariant Set.empty m) m}


(***** Following lemmas are needed in Steel.Effect *****)

val core_mem_interp (hp:slprop u#a) (m:mem u#a)
    : Lemma
      (requires interp hp m)
      (ensures interp hp (core_mem m))
      [SMTPat (interp hp (core_mem m))]

val interp_depends_only_on (hp:slprop u#a)
    : Lemma
      (forall (m0:hmem hp) (m1:mem u#a{disjoint m0 m1}).
        interp hp m0 <==> interp hp (join m0 m1))

let affine_star_smt (p q:slprop u#a) (m:mem u#a)
    : Lemma (interp (p `star` q) m ==> interp p m /\ interp q m)
      [SMTPat (interp (p `star` q) m)]
    = affine_star p q m

val h_exists_cong (#a:Type) (p q : a -> slprop)
    : Lemma
      (requires (forall x. p x `equiv` q x))
      (ensures (h_exists p `equiv` h_exists q))

////////////////////////////////////////////////////////////////////////////////
// Actions:
////////////////////////////////////////////////////////////////////////////////

(** A memory predicate that depends only on fp *)
let mprop (fp:slprop u#a) =
  q:(mem u#a -> prop){
    forall (m0:mem{interp fp m0}) (m1:mem{disjoint m0 m1}).
      q m0 <==> q (join m0 m1)}

let pre_action (fp:slprop u#a) (a:Type u#b) (fp':a -> slprop u#a) =
  hmem_with_inv fp -> (x:a & hmem_with_inv (fp' x))

val ac_reasoning_for_m_frame_preserving
    (p q r:slprop u#a) (m:mem u#a)
  : Lemma
    (requires interp ((p `star` q) `star` r) m)
    (ensures interp (p `star` r) m)

let is_frame_preserving
  (#a:Type u#b)
  (#fp:slprop u#a)
  (#fp':a -> slprop u#a)
  (f:pre_action u#a u#b fp a fp') =
  forall (frame:slprop u#a) (m0:hmem_with_inv (fp `star` frame)).
    (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
     let (| x, m1 |) = f m0 in
     interp ((fp' x `star` frame) `star` locks_invariant Set.empty m1) m1 /\
     (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1)))

let action (fp:slprop u#a) (a:Type u#b) (fp':a -> slprop u#a) =
  f:pre_action fp a fp'{ is_frame_preserving f }

val sel_action (#a:_) (#pcm:_) (r:ref a pcm) (v0:erased a)
  : action (pts_to r v0) (v:a{compatible pcm v0 v}) (fun _ -> pts_to r v0)

val upd_action (#a:_) (#pcm:_) (r:ref a pcm)
               (v0:FStar.Ghost.erased a)
               (v1:a {Steel.PCM.frame_preserving pcm v0 v1})
  : action (pts_to r v0) unit (fun _ -> pts_to r v1)
