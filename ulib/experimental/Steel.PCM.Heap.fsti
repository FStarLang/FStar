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

/// This module defines the behavior of a structured heap where each memory cell is governed by
/// a partial commutative monoid. This PCM structure is reused for the entire heap as it is possible
/// to talk about disjoint heaps and join them together.
///
/// In a sense, a heap here can be seen as a partial heap, containing a partial view of the state of
/// the memory. Combining disjoint heaps is then equivalent to conciling two partial views of the
/// memory together. This is our base for separation logic.
///
/// The heap is instrumented with affine heap predicates, heap predicates that don't change if you
/// augment the heap on which they're valid by joining another partial heap. These affine heap
/// predicates are the terms of our separation logic.
///
/// Finally, the module defines actions for heap, which are frame-preserving heap updates.

(**** The base : partial heaps *)

(**
  Abstract type of heaps. Can conceptually be thought of as a map from addresses to
  contents of memory cells.
*)
val heap  : Type u#(a + 1)

(** A [ref a pcm] is a key into the [heap], containing a value of type [a] governed by the [pcm] *)
val ref (a:Type u#a) (pcm:pcm a) : Type u#0

(** The predicate describing non-overlapping heaps *)
val disjoint (h0 h1:heap u#h) : prop

(** Disjointness is symmetric *)
val disjoint_sym (h0 h1:heap u#h)
  : Lemma (disjoint h0 h1 <==> disjoint h1 h0)
          [SMTPat (disjoint h0 h1)]

(** Disjoint heaps can be combined into a bigger heap*)
val join (h0:heap u#h) (h1:heap u#h{disjoint h0 h1}) : heap u#h

(** The join operation is commutative *)
val join_commutative (h0 h1:heap)
  : Lemma
    (requires
      disjoint h0 h1)
    (ensures
      (disjoint_sym h0 h1;
       join h0 h1 == join h1 h0))

(** Disjointness distributes over join *)
val disjoint_join (h0 h1 h2:heap)
  : Lemma (disjoint h1 h2 /\
           disjoint h0 (join h1 h2) ==>
           disjoint h0 h1 /\
           disjoint h0 h2 /\
           disjoint (join h0 h1) h2 /\
           disjoint (join h0 h2) h1)

(** Join is associative *)
val join_associative (h0 h1 h2:heap)
  : Lemma
    (requires
      disjoint h1 h2 /\
      disjoint h0 (join h1 h2))
    (ensures
      (disjoint_join h0 h1 h2;
       join h0 (join h1 h2) == join (join h0 h1) h2))

(**** Separation logic over heaps *)

(**
  An affine heap proposition or affine heap predicate is a proposition whose validity does not
  change if the heap on which it is valid grows. In other terms, it is a proposition that is
  compatible with the disjoint/join operations for partial heaps. These affine heap predicates
  are the base of our separation logic.
*)
let heap_prop_is_affine (p:heap u#a -> prop) : prop =
  forall (h0 h1: heap u#a). p h0 /\ disjoint h0 h1 ==> p (join h0 h1)

(**
  An affine heap proposition
  *)
let a_heap_prop = p:(heap -> prop) { heap_prop_is_affine p }

(**
  [slprop] is an abstract "separation logic proposition"

  The [erasable] attribute says that it is computationally irrelevant
  and will be extracted to [()]
*)
[@@erasable]
val slprop : Type u#(a + 1)

(**
  [slprop]s can be "interpreted" over any heap, yielding a [prop]
*)
val interp (p:slprop u#a) (m:heap u#a) : prop

(**
  Promoting an affine heap proposition to an slprop
  *)
val as_slprop (f:a_heap_prop) : p:slprop{forall h.interp p h <==> f h}

(**
  An [hprop] is heap predicate indexed by a footprint [fp:slprop].
  Its validity depends only on the fragment of the heap that satisfies [fp].
  Note, it is unrelated to affinity, since the forward implication only applies
  to heaps [h0] that validate [fp]
*)
let hprop (fp:slprop u#a) =
  q:(heap u#a -> prop){
    forall (h0:heap{interp fp h0}) (h1:heap{disjoint h0 h1}).
      q h0 <==> q (join h0 h1)
  }

(** A common abbreviation: [hheap p] is a heap on which [p] is valid *)
let hheap (p:slprop u#a) = m:heap u#a {interp p m}

(**
  Equivalence relation on [slprop]s is just
  equivalence of their interpretations
*)
let equiv (p1 p2:slprop) =
  forall m. interp p1 m <==> interp p2 m

/// We can now define all the standard connectives of separation logic

(** [emp] is the empty [slprop], valid on all heaps. It acts as the unit element *)
val emp : slprop u#a
(** "Points to" allows to talk about the heap contents *)
val pts_to (#a:Type u#a) (#pcm:_) (r:ref a pcm) (v:a) : slprop u#a
val h_and (p1 p2:slprop u#a) : slprop u#a
val h_or  (p1 p2:slprop u#a) : slprop u#a
val star  (p1 p2:slprop u#a) : slprop u#a
val wand  (p1 p2:slprop u#a) : slprop u#a
val h_exists (#a:Type u#b) (f: (a -> slprop u#a)) : slprop u#a
val h_forall (#a:Type u#b) (f: (a -> slprop u#a)) : slprop u#a
(**
  [h_refine] consists of refining a separation logic proposition [p] with an affine heap predicate
  [r]. Since both types are equal, this is equivalent to [h_and].
*)
val h_refine (p:slprop u#a) (r:a_heap_prop u#a) : slprop u#a

(***** Basic properties of separation logic *)

(** If [p * q] is valid on [h], then [p] and [q] are valid on [h] *)
val affine_star (p q:slprop) (h:heap)
  : Lemma ((interp (p `star` q) h ==> interp p h /\ interp q h))

(** Equivalence of separation logic propositions is symmetric *)
val equiv_symmetric (p1 p2:slprop)
  : squash (p1 `equiv` p2 ==> p2 `equiv` p1)

(** If [p1 ~ p2] then [p1 * p3 ~ p2 * p3] *)
val equiv_extensional_on_star (p1 p2 p3:slprop)
  : squash (p1 `equiv` p2 ==> (p1 `star` p3) `equiv` (p2 `star` p3))

(** [p ~~ p * emp] *)
val emp_unit (p:slprop)
  : Lemma (p `equiv` (p `star` emp))

(** [emp] is trivial *)
val intro_emp (h:heap)
  : Lemma (interp emp h)

(** Introduction rule for equivalence of [h_exists] propositions *)
val h_exists_cong (#a:Type) (p q : a -> slprop)
    : Lemma
      (requires (forall x. p x `equiv` q x))
      (ensures (h_exists p `equiv` h_exists q))

(**
  The interpretation of a separation logic proposition [hp] is itself an [hprop] of footprint
  [hp]
*)
val interp_depends_only_on (hp:slprop u#a)
    : Lemma
      (forall (h0:hheap hp) (h1:heap u#a{disjoint h0 h1}).
        interp hp h0 <==> interp hp (join h0 h1))


(***** [pts_to] properties *)

(**
  [ptr r] is a separation logic proposition asserting the existence of an allocated cell at
  reference [r]
*)
let ptr (#a: Type u#a) (#pcm: pcm a) (r:ref a pcm) =
    h_exists (pts_to r)

(**
  If we have [pts_to x v0] and [pts_to y v1] on the same heap, then [v0] and [v1] are are related
  by the PCM governing [x]. Indeed, the [pts_to] predicate is not stricly injective, as our partial
  heaps offer only a partial view on the contents of the memory cell. This partial view is governed
  by [pcm], and this lemma shows that you can combine two [pts_to] predicates into a third, with
  a new value with is the composition of [v0] and [v1] by [pcm].
  This lemma is equivalent to injectivity of [pts_to] if you instantiate [pcm] with the exclusive
  PCM.
*)
val pts_to_compatible
  (#a:Type u#a)
  (#pcm: pcm a)
  (x:ref a pcm)
  (v0 v1:a)
  (h:heap u#a)
    : Lemma
      (interp (pts_to x v0 `star` pts_to x v1) h
       <==>
       (composable pcm v0 v1 /\
        interp (pts_to x (op pcm v0 v1)) h))

val pts_to_compatible_equiv (#a:Type) (#pcm:_) (x:ref a pcm) (v0:a) (v1:a{composable pcm v0 v1})
  : Lemma (equiv (pts_to x v0 `star` pts_to x v1)
                 (pts_to x (op pcm v0 v1)))

(***** Properties of separating conjunction *)

(** The separating conjunction [star] arises from the disjointness of partial heaps *)
val intro_star (p q:slprop) (hp:hheap p) (hq:hheap q)
    : Lemma
      (requires disjoint hp hq)
      (ensures interp (p `star` q) (join hp hq))

(** [star] is commutative *)
val star_commutative (p1 p2:slprop)
    : Lemma ((p1 `star` p2) `equiv` (p2 `star` p1))

(** [star] is associative *)
val star_associative (p1 p2 p3:slprop)
    : Lemma (
      (p1 `star` (p2 `star` p3))
      `equiv`
      ((p1 `star` p2) `star` p3)
    )

(** If [p1 ~ p3] and [p2 ~ p4], then [p1 * p2 ~ p3 * p4] *)
val star_congruence (p1 p2 p3 p4:slprop)
  : Lemma (requires p1 `equiv` p3 /\ p2 `equiv` p4)
          (ensures (p1 `star` p2) `equiv` (p3 `star` p4))

(***** Properties of the refinement *)

(** [h_refine p q] is just interpreting the affine heap prop [q] when [p] is valid *)
val refine_interp (p:slprop u#a) (q:a_heap_prop u#a) (h:heap u#a)
    : Lemma (interp p h /\ q h <==> interp (h_refine p q) h)

(**
  Equivalence on [h_refine] propositions is define by logical equivalence of the refinements
  on all heaps
*)
val refine_equiv (p0 p1:slprop u#a) (q0 q1:a_heap_prop u#a)
    : Lemma (p0 `equiv` p1 /\ (forall h. q0 h <==> q1 h) ==>
             equiv (h_refine p0 q0) (h_refine p1 q1))

(**
  A [pure] separation logic predicate is a refinement on the empty heap. That is how we
  lift pure propositions to the separation logic world
*)
let pure (p:prop) = h_refine emp (fun _ -> p)

(** Equivalence of pure propositions is the equivalence of the underlying propositions *)
val pure_equiv (p q:prop)
  : Lemma ((p <==> q) ==> (pure p `equiv` pure q))

(** And the interpretation of pure propositions is their underlying propositions *)
val pure_interp (q:prop) (h:heap u#a)
   : Lemma (interp (pure q) h <==> q)

(** A helper lemma for interpreting a pure proposition with another [slprop] *)
val pure_star_interp (p:slprop u#a) (q:prop) (h:heap u#a)
   : Lemma (interp (p `star` pure q) h <==>
            interp (p `star` emp) h /\ q)

(***** Magic wand and implications properties *)

(** We can define a [stronger] relation on [slprops], defined by interpretation implication *)
let stronger (p q:slprop) =
  forall h. interp p h ==> interp q h

(** [stronger] is stable when adding another starred [slprop] *)
val stronger_star (p q r:slprop)
  : Lemma (stronger q r ==> stronger (p `star` q) (p `star` r))

(** If [q > r] and [p * q] is valid, then [p * r] is valid *)
val weaken (p q r:slprop) (h:heap u#a)
  : Lemma (q `stronger` r /\ interp (p `star` q) h ==> interp (p `star` r) h)

(**** Actions *)

(**
  This modules exposes a preorder that is respected for every well-formed update of the heap.
  The preorder represents the fact that once a reference is allocated, its type and PCM cannot
  change and the trace of values contained in the PCM respects the preorder induced by the
  PCM (see Steel.PCM.Preorder).
*)
val heap_evolves : FStar.Preorder.preorder heap

(**
  This predicate allows us to maintain an allocation counter, as all references above [a]
  in [h] are free.
*)
val free_above_addr (h:heap u#a) (a:nat) : prop

(** [free_above_addr] is abstract but can be weakened consistently with its intended behavior *)
val weaken_free_above (h:heap) (a b:nat)
  : Lemma (free_above_addr h a /\ a <= b ==> free_above_addr h b)

(**
  The base type for an action is indexed by two separation logic propositions, representing
  the heap specification of the action before and after.
*)
let pre_action (fp:slprop u#a) (a:Type u#b) (fp':a -> slprop u#a) =
  hheap fp -> (x:a & hheap (fp' x))

(**
  We only want to consider heap updates that are "frame-preserving", meaning that they only
  modify the portion of the heap that they're allowed to, without messing with any other
  partial view of the heap that is compatible with the one you own. This includes :
  - preserving correct interpretation in presence of a frame;
  - evolving the heap according to the heap preorder;
  - not allocating any new references;
  - preserving the validity of any heap proposition affecting any frame
*)
let is_frame_preserving
  (#a: Type u#a)
  (#fp: slprop u#b)
  (#fp': a -> slprop u#b)
  (f:pre_action fp a fp')
  =
  forall (frame: slprop u#b) (h0:hheap (fp `star` frame)).
     (affine_star fp frame h0;
      let (| x, h1 |) = f h0 in
      interp (fp' x `star` frame) h1 /\
      heap_evolves h0 h1 /\
      (forall ctr. h0 `free_above_addr` ctr ==> h1 `free_above_addr` ctr) /\
      (forall (hp:hprop frame). hp h0 == hp h1))

(**
  Two heaps [h0] and [h1] are frame-related if you can get from [h0] to [h1] with a
  frame-preserving update.
*)
let frame_related_heaps (h0 h1:heap) (fp0 fp1 frame:slprop) (allocates:bool) =
  interp (fp0 `star` frame) h0 ==>
  interp (fp1 `star` frame) h1 /\
  heap_evolves h0 h1 /\
  (forall (hp:hprop frame). hp h0 == hp h1) /\
  (not allocates ==> (forall ctr. h0 `free_above_addr` ctr ==> h1 `free_above_addr` ctr))

(** Every action is frame-preserving *)
let action (fp:slprop u#b) (a:Type u#a) (fp':a -> slprop u#b) =
  f:pre_action fp a fp'{ is_frame_preserving f }

(**
  A frame-preserving action applied on [h0] produces an [h1] such that [h0] and [h1] are
  frame-related
*)
let action_framing
  (#a: Type u#a)
  (#fp: slprop u#b)
  (#fp': a -> slprop u#b)
  ($f:action fp a fp')
  (frame:slprop) (h0:hheap (fp `star` frame))
    : Lemma (
      affine_star fp frame h0;
      let (| x, h1 |) = f h0 in
      frame_related_heaps h0 h1 fp (fp' x) frame false
    )
  =
  affine_star fp frame h0;
  emp_unit fp

(** [sel] is a ghost read of the value contained in a heap reference *)
val sel (#a:Type u#h) (#pcm:pcm a) (r:ref a pcm) (m:hheap (ptr r)) : a

(** [sel] respect [pts_to] *)
val sel_lemma (#a:_) (#pcm:_) (r:ref a pcm) (m:hheap (ptr r))
  : Lemma (interp (pts_to r (sel r m)) m)

(**
  The action variant of [sel], returning the "true" value inside the heap. This "true" value
  can be different of the [pts_to] value you assumed at the beginning, because of the PCM structure
*)
val sel_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:erased a)
    : action (pts_to r v0) (v:a{compatible pcm v0 v}) (fun _ -> pts_to r v0)

(**
  The update action needs you to prove that the mutation from [v0] to [v1] is frame-preserving
  with respect to the individual PCM governing the reference [r]. See [Steel.PCM.frame_preserving]
*)
val upd_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:a {Steel.PCM.frame_preserving pcm v0 v1})
    : action (pts_to r v0) unit (fun _ -> pts_to r v1)

(** Deallocating a reference, by actually replacing its value by the unit of the PCM *)
val free_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a {exclusive pcm v0})
  : action (pts_to r v0) unit (fun _ -> pts_to r pcm.Steel.PCM.p.one)


(** Splitting a permission on a composite resource into two separate permissions *)
val split_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a{composable pcm v0 v1})
  : action (pts_to r (v0 `op pcm` v1)) unit (fun _ -> pts_to r v0 `star` pts_to r v1)

(** Combining separate permissions into a single composite permission *)
val gather_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a)
  : action (pts_to r v0 `star` pts_to r v1) (_:unit{composable pcm v0 v1}) (fun _ -> pts_to r (op pcm v0 v1))

(** Allocating is a pseudo action here, the context needs to provide a fresh address *)
val extend
  (#a:Type u#a)
  (#pcm:pcm a)
  (x:a{compatible pcm x x})
  (addr:nat)
  (h:heap{h `free_above_addr` addr})
  : (
    r:ref a pcm
    & h':heap{
      (forall (frame: slprop u#a).
        frame_related_heaps h h' emp (pts_to r x) frame (true)) /\
        h' `free_above_addr` (addr + 1) /\
        heap_evolves h h'
    }
  )

val frame (#a:Type)
          (#pre:slprop)
          (#post:a -> slprop)
          (frame:slprop)
          ($f:action pre a post)
  : action (pre `star` frame) a (fun x -> post x `star` frame)

val change_slprop (p q:slprop)
                  (proof: (h:heap -> Lemma (requires interp p h) (ensures interp q h)))
  : action p unit (fun _ -> q)
