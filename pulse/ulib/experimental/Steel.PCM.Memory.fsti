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
val heap  : Type u#(a + 1)

/// A memory maps a reference to its associated value
val ref (a:Type u#a) (pcm:pcm a) : Type u#0

/// A predicate describing non-overlapping memories
val disjoint (m0 m1:heap u#h) : prop

/// disjointness is symmetric
val disjoint_sym (m0 m1:heap u#h)
  : Lemma (disjoint m0 m1 <==> disjoint m1 m0)
          [SMTPat (disjoint m0 m1)]

/// disjoint memories can be combined
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

/// The type of heap assertions
[@erasable]
val slprop : Type u#(a + 1)

/// interpreting heap assertions as memory predicates
val interp (p:slprop u#a) (m:heap u#a) : prop

/// A common abbreviation: memories validating p
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

////////////////////////////////////////////////////////////////////////////////
//properties of equiv
////////////////////////////////////////////////////////////////////////////////

val equiv_symmetric (p1 p2:slprop)
  : squash (p1 `equiv` p2 ==> p2 `equiv` p1)

val equiv_extensional_on_star (p1 p2 p3:slprop)
  : squash (p1 `equiv` p2 ==> (p1 `star` p3) `equiv` (p2 `star` p3))


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
      combinable pcm v0 v1 /\
      interp (pts_to x (pcm.op v0 v1)) m)

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

////////////////////////////////////////////////////////////////////////////////
// Actions:
// sel, split, update
////////////////////////////////////////////////////////////////////////////////
let pre_action (fp:slprop) (a:Type) (fp':a -> slprop) =
  hheap fp -> (x:a & hheap (fp' x))

let is_frame_preserving #a #fp #fp' (f:pre_action fp a fp') =
  forall frame h0.
    interp (fp `star` frame) h0 ==>
    (let (| x, h1 |) = f h0 in
     interp (fp' x `star` frame) h1)

let depends_only_on (q:heap -> prop) (fp: slprop) =
  (forall h0 h1. q h0 /\ disjoint h0 h1 ==> q (join h0 h1)) /\
  (forall (h0:hheap fp) (h1:heap{disjoint h0 h1}). q h0 <==> q (join h0 h1))

let fp_prop fp = p:(heap -> prop){p `depends_only_on` fp}

let action_depends_only_on_fp (#pre:_) (#a:_) (#post:_) (f:pre_action pre a post)
  = forall (h0:hheap pre)
      (h1:heap {disjoint h0 h1})
      (post: (x:a -> fp_prop (post x))).
      (interp pre (join h0 h1) /\ (
       let (| x0, h |) = f h0 in
       let (| x1, h' |) = f (join h0 h1) in
       x0 == x1 /\
       (post x0 h <==> post x1 h')))

let action (fp:slprop) (a:Type) (fp':a -> slprop) =
  f:pre_action fp a fp'{ is_frame_preserving f }

val sel (#a:_) (#pcm:_) (r:ref a pcm) (m:hheap (ptr r))
  : a

/// sel respect pts_to
val sel_lemma (#a:_) (#pcm:_) (r:ref a pcm) (m:hheap (ptr r))
  : Lemma (interp (pts_to r (sel r m)) m)

val sel_action (#a:_) (#pcm:_) (r:ref a pcm) (v0:erased a)
  : action (pts_to r v0) (v:a{compatible pcm v0 v}) (fun _ -> pts_to r v0)

/// updating a ref cell from v0 to v1
/// must be compatible with other views of the same cell
val upd (#a:_) (#pcm:_) (r:ref a pcm) (v0:FStar.Ghost.erased a) (v1:a {Steel.PCM.frame_preserving pcm v0 v1})
  : action (pts_to r v0) unit (fun _ -> pts_to r v1)

////////////////////////////////////////////////////////////////////////////////
// wand
////////////////////////////////////////////////////////////////////////////////

/// A low-level introduction form for wand in terms of disjoint
val intro_wand_alt (p1 p2:slprop) (m:heap)
  : Lemma
    (requires
      (forall (m0:hheap p1).
         disjoint m0 m ==>
         interp p2 (join m0 m)))
    (ensures
      interp (wand p1 p2) m)

/// A higher-level introduction for wand as a cut
val intro_wand (p q r:slprop) (m:hheap q)
  : Lemma
    (requires
      (forall (m:hheap (p `star` q)). interp r m))
    (ensures
      interp (p `wand` r) m)

/// Standard wand elimination
val elim_wand (p1 p2:slprop) (m:heap)
  : Lemma
    (requires
      (interp ((p1 `wand` p2) `star` p1) m))
    (ensures
      interp p2 m)

////////////////////////////////////////////////////////////////////////////////
// or
////////////////////////////////////////////////////////////////////////////////
val intro_or_l (p1 p2:slprop) (m:hheap p1)
  : Lemma (interp (h_or p1 p2) m)

val intro_or_r (p1 p2:slprop) (m:hheap p2)
  : Lemma (interp (h_or p1 p2) m)

/// star can be factored out of or
val or_star (p1 p2 p:slprop) (m:hheap ((p1 `star` p) `h_or` (p2 `star` p)))
  : Lemma (interp ((p1 `h_or` p2) `star` p) m)

/// A standard or eliminator
val elim_or (p1 p2 q:slprop) (m:hheap (p1 `h_or` p2))
  : Lemma (((forall (m:hheap p1). interp q m) /\
            (forall (m:hheap p2). interp q m)) ==> interp q m)


////////////////////////////////////////////////////////////////////////////////
// and
////////////////////////////////////////////////////////////////////////////////
val intro_and (p1 p2:slprop) (m:heap)
  : Lemma (interp p1 m /\
           interp p2 m ==>
           interp (p1 `h_and` p2) m)

val elim_and (p1 p2:slprop) (m:hheap (p1 `h_and` p2))
  : Lemma (interp p1 m /\
           interp p2 m)

////////////////////////////////////////////////////////////////////////////////
// h_exists
////////////////////////////////////////////////////////////////////////////////

val intro_exists (#a:_) (x:a) (p : a -> slprop) (m:hheap (p x))
  : Lemma (interp (h_exists p) m)

val elim_exists (#a:_) (p:a -> slprop) (q:slprop) (m:hheap (h_exists p))
  : Lemma
    ((forall (x:a). interp (p x) m ==> interp q m) ==>
     interp q m)


////////////////////////////////////////////////////////////////////////////////
// h_forall
////////////////////////////////////////////////////////////////////////////////

val intro_forall (#a:_) (p : a -> slprop) (m:heap)
  : Lemma ((forall x. interp (p x) m) ==> interp (h_forall p) m)

val elim_forall (#a:_) (p : a -> slprop) (m:hheap (h_forall p))
  : Lemma ((forall x. interp (p x) m) ==> interp (h_forall p) m)

////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////

val affine_star (p q:slprop) (m:heap)
  : Lemma
    (ensures (interp (p `star` q) m ==> interp p m /\ interp q m))

////////////////////////////////////////////////////////////////////////////////
// emp
////////////////////////////////////////////////////////////////////////////////
val intro_emp (m:heap)
  : Lemma (interp emp m)

val emp_unit (p:slprop)
  : Lemma ((p `star` emp) `equiv` p)

////////////////////////////////////////////////////////////////////////////////
// refinement
////////////////////////////////////////////////////////////////////////////////

val weaken_depends_only_on (q:heap -> prop) (fp fp': slprop)
  : Lemma (depends_only_on q fp ==> depends_only_on q (fp `star` fp'))

val refine (p:slprop) (q:fp_prop p) : slprop

val refine_equiv (p:slprop) (q:fp_prop p) (h:heap)
  : Lemma (interp p h /\ q h <==> interp (refine p q) h)

val refine_star (p0 p1:slprop) (q:fp_prop p0)
  : Lemma (weaken_depends_only_on q p0 p1;
           equiv (refine (p0 `star` p1) q) (refine p0 q `star` p1))

val interp_depends_only (p:slprop)
  : Lemma (interp p `depends_only_on` p)

val frame_fp_prop (#fp:_) (#a:Type) (#fp':_) (act:action fp a fp')
                  (#frame:slprop) (q:fp_prop frame)
   : Lemma (forall (h0:hheap (fp `star` frame)).
              (affine_star fp frame h0;
               q h0 ==>
               (let (| x, h1 |) = act h0 in
                q h1)))

////////////////////////////////////////////////////////////////////////////////
// Allocation
////////////////////////////////////////////////////////////////////////////////
val mem : Type u#(a + 3)
val heap_of_mem (x:mem u#(a + 3)) : heap u#(a + 1)

val alloc (#a:_) (pcm:pcm a) (v:a)
          (frame:slprop)
          (tmem:mem{interp frame (heap_of_mem tmem)})
  : (x:ref a pcm &
     tmem:mem { interp (pts_to x v `star` frame) (heap_of_mem tmem)} )
