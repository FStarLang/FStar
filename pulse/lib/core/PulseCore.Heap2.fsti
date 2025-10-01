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
module PulseCore.Heap2
open FStar.Ghost
open FStar.PCM
open PulseCore.Tags
module T = FStar.Tactics
module H = PulseCore.Heap
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
val concrete (h:heap u#a) : H.heap u#a
val ghost (h:heap u#a) : erased (H.heap u#a)
val upd_ghost_heap (h0:heap) (h1:erased heap { concrete h0 == concrete h1 })
  : h2:heap { h2 == reveal h1 }

(* An empty heap *)
val empty_heap : heap u#a

(** A [core_ref] is a key into the [heap] or [null] *)
val core_ref : Type u#0

val core_ref_as_addr (_:core_ref) : GTot nat

(** We index a [core_ref] by the type of its heap contents
    and a [pcm] governing it, for ease of type inference *)
let ref (a:Type u#a) (pcm:pcm a) : Type u#0 = core_ref

val core_ref_null : core_ref

(** [null] is a specific reference, that is not associated to any value
*)
let null (#a:Type u#a) (#pcm:pcm a) : ref a pcm = core_ref_null

(** Checking whether [r] is the null pointer is decidable through [is_null]
*)
val core_ref_is_null (r:core_ref) : b:bool { b <==> r == core_ref_null }

(** Checking whether [r] is the null pointer is decidable through [is_null]
*)
let is_null (#a:Type u#a) (#pcm:pcm a) (r:ref a pcm) : (b:bool{b <==> r == null}) = core_ref_is_null r

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
      (disjoint h1 h0 /\
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
      (disjoint h0 h1 /\
       disjoint (join h0 h1) h2 /\
       join h0 (join h1 h2) == join (join h0 h1) h2))

val join_empty (h:heap)
  : Lemma (disjoint h empty_heap /\
           join h empty_heap == h)

val join_empty_inverse (m0 m1:heap)
: Lemma 
  (requires disjoint m0 m1 /\ join m0 m1 == empty_heap)
  (ensures m0 == empty_heap /\ m1 == empty_heap)

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

(**
  An extensional equivalence principle for slprop
 *)
val slprop_extensionality (p q:slprop)
  : Lemma
    (requires p `equiv` q)
    (ensures p == q)

/// We can now define all the standard connectives of separation logic

(** [emp] is the empty [slprop], valid on all heaps. It acts as the unit element *)
val emp : slprop u#a
(** "Points to" allows to talk about the heap contents *)
val pts_to (#a:Type u#a) (#pcm:_) (r:ref a pcm) (v:a) : slprop u#a
val star  (p1 p2:slprop u#a) : slprop u#a
val h_exists (#[@@@strictly_positive] a:Type u#b)
             ([@@@strictly_positive]  f: (a -> slprop u#a))
  : slprop u#a

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

(** If a reference points to two different values, they must be joinable
in the PCM, even when the pointing does not happen separately. *)
val pts_to_join (#a:Type u#a) (#pcm:_) (r:ref a pcm) (v1 v2:a) (m:heap)
  : Lemma (requires (interp (pts_to r v1) m /\ interp (pts_to r v2) m))
          (ensures joinable pcm v1 v2)

(** Further, the value in the heap is a witness for that property *)
val pts_to_join' (#a:Type u#a) (#pcm:_) (r:ref a pcm) (v1 v2:a) (m:heap)
  : Lemma (requires (interp (pts_to r v1) m /\ interp (pts_to r v2) m))
          (ensures (exists z. compatible pcm v1 z /\ compatible pcm v2 z /\
                         interp (pts_to r z) m))

val pts_to_compatible_equiv (#a:Type)
                            (#pcm:_)
                            (x:ref a pcm)
                            (v0:a)
                            (v1:a{composable pcm v0 v1})
  : Lemma (equiv (pts_to x v0 `star` pts_to x v1)
                 (pts_to x (op pcm v0 v1)))

val pts_to_not_null (#a:Type)
                    (#pcm:_)
                    (x:ref a pcm)
                    (v:a)
                    (m:heap)
  : Lemma (requires interp (pts_to x v) m)
          (ensures x =!= null)

(***** Properties of separating conjunction *)

(** The separating conjunction [star] arises from the disjointness of partial heaps *)
val intro_star (p q:slprop) (hp:hheap p) (hq:hheap q)
    : Lemma
      (requires disjoint hp hq)
      (ensures interp (p `star` q) (join hp hq))

val elim_star (p q:slprop) (h:hheap (p `star` q))
    : Lemma
      (requires interp (p `star` q) h)
    (ensures exists hl hr.
      disjoint hl hr /\
      h == join hl hr /\
      interp p hl /\
      interp q hr)

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

(**
  A [pure] separation logic predicate is a refinement on the empty heap. That is how we
  lift pure propositions to the separation logic world
*)
val pure (p:prop) : slprop

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

(**** Actions *)

(** An abstract predicate classifying a "full" heap, i.e., the entire
    heap of the executing program, not just a fragment of it *)
val full_heap_pred : heap -> prop

let full_heap = h:heap { full_heap_pred h }

let full_hheap fp = h:hheap fp { full_heap_pred h }

(**
  This predicate allows us to maintain an allocation counter, as all references above [a]
  in [h] are free.
*)
val select (i:nat) (m:heap u#a) : GTot (option (H.cell u#a))
val select_ghost (i:nat) (m:heap u#a) : GTot (option (H.cell u#a))
val select_ghost_interp (i:nat) (h:heap u#a)
: Lemma (select_ghost i h == H.select i (ghost h))
let select_either (t:tag) (i:nat) (h:heap) : GTot (option H.cell) = 
  match t with
  | CONCRETE -> select i h
  | GHOST -> select_ghost i h

(**
  The base type for an action is indexed by two separation logic propositions, representing
  the heap specification of the action before and after.
*)
let trivial_pre (h:heap) : prop = True

let pre_action (fp:slprop u#a)
               (a:Type u#b)
               (fp':a -> slprop u#a)
  = h0:full_hheap fp -> (x:a & full_hheap (fp' x))

(**
  This is how the heaps before and after the action relate:
  - evolving the heap according to the heap preorder;
  - preserving the validity of any heap proposition affecting any frame
*)
let no_allocs : option tag = None
  
unfold
let action_related_heaps 
      (#[T.exact (`MUTABLE)] m:mutability)
      (h0 h1:full_heap) =
  match m with
  | ONLY_GHOST ->
    concrete h0 == concrete h1
  | IMMUTABLE ->
    h0 == h1
  | _ -> True


(**
  We only want to consider heap updates that are "frame-preserving", meaning that they only
  modify the portion of the heap that they're allowed to, without messing with any other
  partial view of the heap that is compatible with the one you own. This includes :
  - preserving correct interpretation in presence of a frame;
  - heaps are related as defined above
*)
let is_frame_preserving
  (#a: Type u#a)
  (#fp: slprop u#b)
  (#fp': a -> slprop u#b)
  (immut:mutability)
  (f:pre_action fp a fp')
  =
  forall (frame: slprop u#b) (h0:full_hheap (fp `star` frame)).
     (affine_star fp frame h0;
      let (| x, h1 |) = f h0 in
      interp (fp' x `star` frame) h1 /\
      action_related_heaps #immut h0 h1)

(** Every action is frame-preserving *)
let action (#[T.exact (`MUTABLE)] mut:mutability)
           (fp:slprop u#b) (a:Type u#a) (fp':a -> slprop u#b) =
  f:pre_action fp a fp'{ is_frame_preserving mut f }

let apply_action #mut #fp (#a: Type u#a) #fp'
    (act: action #mut fp a fp')
    (frame: slprop u#b) (h0: full_hheap (fp `star` frame))
  : x:a & h1:full_hheap (fp' x `star` frame) { action_related_heaps #mut h0 h1 } =
  affine_star fp frame h0;
  let (| x, h1 |) = act h0 in
  (| x, h1 |)

(**
  Two heaps [h0] and [h1] are frame-related if you can get from [h0] to [h1] with a
  frame-preserving update.
*)
let frame_related_heaps (h0 h1:full_heap) (fp0 fp1 frame:slprop)
                        (mut:mutability) =
  interp (fp0 `star` frame) h0 ==>
  interp (fp1 `star` frame) h1 /\
  action_related_heaps #mut h0 h1


(**
  A frame-preserving action applied on [h0] produces an [h1] such that [h0] and [h1] are
  frame-related
*)
let action_framing
  (#a: Type u#a)
  (#mut:_)
  (#fp: slprop u#b)
  (#fp': a -> slprop u#b)
  ($f:action #mut fp a fp')
  (frame:slprop) (h0:full_hheap (fp `star` frame))
    : Lemma (
      affine_star fp frame h0;
      let (| x, h1 |) = f h0 in
      frame_related_heaps h0 h1 fp (fp' x) frame mut
    )
  =
  affine_star fp frame h0;
  emp_unit fp


(** [sel] is a ghost read of the value contained in a heap reference *)
val sel (#a:Type u#h) (#pcm:pcm a) (r:ref a pcm) (m:full_hheap (ptr r)) : a

(** [sel_v] is a ghost read of the value contained in a heap reference *)
val sel_v (#a:Type u#h) (#pcm:pcm a) (r:ref a pcm) (v:erased a) (m:full_hheap (pts_to r v))
  : v':a{ compatible pcm v v' /\
          pcm.refine v' /\
          interp (ptr r) m /\
          v' == sel r m }

(** [sel] respect [pts_to] *)
val sel_lemma (#a:_) (#pcm:_) (r:ref a pcm) (m:full_hheap (ptr r))
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
    : action #IMMUTABLE
       (pts_to r v0) (v:a{compatible pcm v0 v}) (fun _ -> pts_to r v0)

(**
  A version of select that incorporates a ghost update of local
  knowledge of a ref cell based on the value that was read
 *)
val select_refine (#a:_) (#p:_)
                  (r:ref a p)
                  (x:erased a)
                  (f:(v:a{compatible p x v}
                      -> GTot (y:a{compatible p y v /\
                                  FStar.PCM.frame_compatible p x v y})))
   : action #IMMUTABLE (pts_to r x)
            (v:a{compatible p x v /\ p.refine v})
            (fun v -> pts_to r (f v))


(** Updating a ref cell for a user-defined PCM *)
val upd_gen_action (#a:Type) (#p:pcm a) (r:ref a p) (x y:Ghost.erased a)
                   (f:FStar.PCM.frame_preserving_upd p x y)
  : action #MUTABLE (pts_to r x)
           unit
           (fun _ -> pts_to r y)

val upd_gen_modifies
      #a (#p:pcm a) 
      (r:ref a p)
      (x y:Ghost.erased a)
      (f:FStar.PCM.frame_preserving_upd p x y)
      (h:full_hheap (pts_to r x))
: Lemma (
      let (| _, h1 |) = upd_gen_action r x y f h in
      (forall (a:nat). a <> core_ref_as_addr r ==> select a h == select a h1) /\
      ghost h == ghost h1 /\
      H.related_cells (select (core_ref_as_addr r) h) (select (core_ref_as_addr r) h1)
  )

(**
  The update action needs you to prove that the mutation from [v0] to [v1] is frame-preserving
  with respect to the individual PCM governing the reference [r]. See [FStar.PCM.frame_preserving]
*)
val upd_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:a {FStar.PCM.frame_preserving pcm v0 v1 /\ pcm.refine v1})
  : action #MUTABLE (pts_to r v0) unit (fun _ -> pts_to r v1)



(** Deallocating a reference, by actually replacing its value by the unit of the PCM *)
val free_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a {exclusive pcm v0 /\ pcm.refine pcm.FStar.PCM.p.one})
  : action #MUTABLE (pts_to r v0) unit (fun _ -> pts_to r pcm.FStar.PCM.p.one)


(** Splitting a permission on a composite resource into two separate permissions *)
val split_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a{composable pcm v0 v1})
  : action #IMMUTABLE (pts_to r (v0 `op pcm` v1)) unit (fun _ -> pts_to r v0 `star` pts_to r v1)

(** Combining separate permissions into a single composite permission *)
val gather_action
  (#a:Type u#a)
  (#pcm:pcm a)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a)
  : action #IMMUTABLE
    (pts_to r v0 `star` pts_to r v1) (_:unit{composable pcm v0 v1}) (fun _ -> pts_to r (op pcm v0 v1))

val pts_to_not_null_action 
      (#a:Type u#a)
      (#pcm:pcm a)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: action #IMMUTABLE
    (pts_to r v)
    (squash (not (is_null r)))
    (fun _ -> pts_to r v)

(** Allocating is a pseudo action here, the context needs to provide a fresh address *)
val extend
  (#a:Type u#a)
  (#pcm:pcm a)
  (x:a{pcm.refine x})
  : action
      #MUTABLE
      emp 
      (ref a pcm)
      (fun r -> pts_to r x)

val extend_modifies
  (#a:Type u#a)
  (#pcm:pcm a)
  (x:a{pcm.refine x})
  (h:full_hheap emp)
: Lemma (
      let (| _, h1 |) = extend #a #pcm x h in
      ghost h == ghost h1
  )

val frame (#a:Type)
          #immut
          (#pre:slprop)
          (#post:a -> slprop)
          (frame:slprop)
          ($f:action #immut pre a post)
  : action #immut (pre `star` frame) a (fun x -> post x `star` frame)

val change_slprop (p q:slprop)
                  (proof: (h:heap -> Lemma (requires interp p h) (ensures interp q h)))
  : action #IMMUTABLE p unit (fun _ -> q)

val elim_pure (p:prop)
  : action #IMMUTABLE (pure p) (u:unit{p}) (fun _ -> emp)

val intro_pure (p:prop) (_:squash p)
  : action #IMMUTABLE emp unit (fun _ -> pure p)

val pts_to_evolve (#a:Type u#a) (#pcm:_) (r:ref a pcm) (x y : a) (h:heap)
  : Lemma (requires (interp (pts_to r x) h /\ compatible pcm y x))
          (ensures  (interp (pts_to r y) h))

val drop (p:slprop)
  : action #IMMUTABLE p unit (fun _ -> emp)

let non_informative (a:Type u#a) =
  x:Ghost.erased a -> y:a{y == Ghost.reveal x}

val lift_erased
          (#a:Type)
          (#ni_a:non_informative a)
          (#mut:mutability { mut == ONLY_GHOST \/ mut == IMMUTABLE })
          (#pre:slprop)
          (#post:a -> slprop)
          ($f:erased (action #mut pre a post))
: action #mut pre a post

[@@erasable]
val core_ghost_ref : Type0
val core_ghost_ref_null : core_ghost_ref
val core_ghost_ref_eq (x y:core_ghost_ref) : GTot (b:bool{b <==> (x==y)})
let ghost_ref (#[@@@unused] a:Type u#a) ([@@@unused]p:pcm a) : Type0 = core_ghost_ref
val ghost_pts_to (#a:Type u#a) (#p:pcm a) (r:ghost_ref p) (v:a) : slprop u#a
val core_ghost_ref_as_addr (_:core_ghost_ref) : GTot nat
val core_ghost_ref_is_null (c:core_ghost_ref) : GTot bool
val addr_as_core_ghost_ref (_:nat) : r:core_ghost_ref { not <| core_ghost_ref_is_null r }
val core_ghost_ref_as_addr_injective (c1:core_ghost_ref)
: Lemma 
  (requires 
    not (core_ghost_ref_is_null c1))
  (ensures
    addr_as_core_ghost_ref (core_ghost_ref_as_addr c1) == c1)
val addr_as_core_ghost_ref_injective (a:nat)
: Lemma 
  (ensures
    core_ghost_ref_as_addr (addr_as_core_ghost_ref a) == a)
val interp_ghost_pts_to 
      (i:core_ghost_ref)
      (#a:Type)
      (#pcm:FStar.PCM.pcm a)
      (v:a)
      (h0:heap)
: Lemma
  (requires interp (ghost_pts_to #a #pcm i v) h0)
  (ensures (
    not (core_ghost_ref_is_null i) /\ (
    match select_ghost (core_ghost_ref_as_addr i) h0 with
    | None -> False
    | Some c ->
      let H.Ref a' pcm' v' = c in
      a == a' /\
      pcm == pcm' /\
      compatible pcm v v')))
      
val ghost_pts_to_compatible_equiv 
      (#a:Type)
      (#pcm:_)
      (x:ghost_ref #a pcm)
      (v0:a)
      (v1:a{composable pcm v0 v1})
: Lemma (equiv (ghost_pts_to x v0 `star` ghost_pts_to x v1)
               (ghost_pts_to x (op pcm v0 v1)))

val ghost_extend
    (#a:Type u#a)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: action #ONLY_GHOST
      emp 
      (ghost_ref pcm)
      (fun r -> ghost_pts_to r x)


val ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: action #IMMUTABLE
    (ghost_pts_to r x)
    (erased (v:a{compatible p x v /\ p.refine v}))
    (fun v -> ghost_pts_to r (f v))

val ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: action #ONLY_GHOST 
    (ghost_pts_to r x)
    unit
    (fun _ -> ghost_pts_to r y)

val ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: action #IMMUTABLE
    (ghost_pts_to r (v0 `op pcm` v1))
    unit
    (fun _ -> ghost_pts_to r v0 `star` ghost_pts_to r v1)

val ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: action #IMMUTABLE 
    (ghost_pts_to r v0 `star` ghost_pts_to r v1)
    (squash (composable pcm v0 v1))
    (fun _ -> ghost_pts_to r (op pcm v0 v1))

val ghost_pts_to_not_null_action 
      (#a:Type u#a)
      (#pcm:pcm a)
      (r:ghost_ref pcm)
      (v:Ghost.erased a)
: action #IMMUTABLE
    (ghost_pts_to r v)
    (squash (r =!= core_ghost_ref_null))
    (fun _ -> ghost_pts_to r v)