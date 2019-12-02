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
module Steel.Memory
open FStar.Real
open Steel.Permissions

/// Abstract type of memories
val heap  : Type u#1

/// A memory maps a reference to its associated value
val ref (a:Type u#0) : Type u#0

/// A predicate describing non-overlapping memories
val disjoint (m0 m1:heap) : prop

/// disjointness is symmetric
val disjoint_sym (m0 m1:heap)
  : Lemma (disjoint m0 m1 <==> disjoint m1 m0)

/// disjoint memories can be combined
val join (m0:heap) (m1:heap{disjoint m0 m1}) : heap

/// disjointness distributes over join
val disjoint_join (m0 m1 m2:heap)
  : Lemma (disjoint m1 m2 /\
           disjoint m0 (join m1 m2) ==>
           disjoint m0 m1 /\
           disjoint m0 m2 /\
           disjoint (join m0 m1) m2 /\
           disjoint (join m0 m2) m1)

val join_commutative (m0 m1:heap)
  : Lemma
    (requires
      disjoint m0 m1)
    (ensures
      (disjoint_sym m0 m1;
       join m0 m1 == join m1 m0))

val join_associative (m0 m1 m2:heap)
  : Lemma
    (requires
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2))
    (ensures
      (disjoint_join m0 m1 m2;
       join m0 (join m1 m2) == join (join m0 m1) m2))

/// The type of heap assertions
val hprop : Type u#1
/// interpreting heap assertions as memory predicates
val interp (p:hprop) (m:heap) : prop

/// A common abbreviation: memories validating p
let hheap (p:hprop) = m:heap{interp p m}

/// Equivalence relation on hprops is just
/// equivalence of their interpretations
let equiv (p1 p2:hprop) =
  forall m. interp p1 m <==> interp p2 m

/// All the standard connectives of separation logic
val emp : hprop
val pts_to (#a:_) (r:ref a) (p:permission) (v:a) : hprop
val h_and (p1 p2:hprop) : hprop
val h_or  (p1 p2:hprop) : hprop
val star  (p1 p2:hprop) : hprop
val wand  (p1 p2:hprop) : hprop
val h_exists (#a:Type0) (f: (a -> hprop)) : hprop
val h_forall (#a:Type0) (f: (a -> hprop)) : hprop

////////////////////////////////////////////////////////////////////////////////
//properties of equiv
////////////////////////////////////////////////////////////////////////////////

val equiv_symmetric (p1 p2:hprop)
  : squash (p1 `equiv` p2 ==> p2 `equiv` p1)

val equiv_extensional_on_star (p1 p2 p3:hprop)
  : squash (p1 `equiv` p2 ==> (p1 `star` p3) `equiv` (p2 `star` p3))


////////////////////////////////////////////////////////////////////////////////
// pts_to and abbreviations
//////////////////////////////////////////////////////////////////////////////////////////
let ptr_perm #a (r:ref a) (p:permission) =
    h_exists (pts_to r p)

let ptr #a (r:ref a) =
    h_exists (ptr_perm r)

val pts_to_injective (#a:_) (x:ref a) (p:permission) (v0 v1:a) (m:heap)
  : Lemma
    (requires
      interp (pts_to x p v0) m /\
      interp (pts_to x p v1) m)
    (ensures
      v0 == v1)

////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////

val intro_star (p q:hprop) (mp:hheap p) (mq:hheap q)
  : Lemma
    (requires
      disjoint mp mq)
    (ensures
      interp (p `star` q) (join mp mq))

val star_commutative (p1 p2:hprop)
  : Lemma ((p1 `star` p2) `equiv` (p2 `star` p1))

val star_associative (p1 p2 p3:hprop)
  : Lemma ((p1 `star` (p2 `star` p3))
           `equiv`
           ((p1 `star` p2) `star` p3))

val star_congruence (p1 p2 p3 p4:hprop)
  : Lemma (requires p1 `equiv` p3 /\ p2 `equiv` p4)
          (ensures (p1 `star` p2) `equiv` (p3 `star` p4))

////////////////////////////////////////////////////////////////////////////////
// wand
////////////////////////////////////////////////////////////////////////////////

/// A low-level introduction form for wand in terms of disjoint
val intro_wand_alt (p1 p2:hprop) (m:heap)
  : Lemma
    (requires
      (forall (m0:hheap p1).
         disjoint m0 m ==>
         interp p2 (join m0 m)))
    (ensures
      interp (wand p1 p2) m)

/// A higher-level introduction for wand as a cut
val intro_wand (p q r:hprop) (m:hheap q)
  : Lemma
    (requires
      (forall (m:hheap (p `star` q)). interp r m))
    (ensures
      interp (p `wand` r) m)

/// Standard wand elimination
val elim_wand (p1 p2:hprop) (m:heap)
  : Lemma
    (requires
      (interp ((p1 `wand` p2) `star` p1) m))
    (ensures
      interp p2 m)

////////////////////////////////////////////////////////////////////////////////
// or
////////////////////////////////////////////////////////////////////////////////
val intro_or_l (p1 p2:hprop) (m:hheap p1)
  : Lemma (interp (h_or p1 p2) m)

val intro_or_r (p1 p2:hprop) (m:hheap p2)
  : Lemma (interp (h_or p1 p2) m)

/// star can be factored out of or
val or_star (p1 p2 p:hprop) (m:hheap ((p1 `star` p) `h_or` (p2 `star` p)))
  : Lemma (interp ((p1 `h_or` p2) `star` p) m)

/// A standard or eliminator
val elim_or (p1 p2 q:hprop) (m:hheap (p1 `h_or` p2))
  : Lemma (((forall (m:hheap p1). interp q m) /\
            (forall (m:hheap p2). interp q m)) ==> interp q m)


////////////////////////////////////////////////////////////////////////////////
// and
////////////////////////////////////////////////////////////////////////////////
val intro_and (p1 p2:hprop) (m:heap)
  : Lemma (interp p1 m /\
           interp p2 m ==>
           interp (p1 `h_and` p2) m)

val elim_and (p1 p2:hprop) (m:hheap (p1 `h_and` p2))
  : Lemma (interp p1 m /\
           interp p2 m)

////////////////////////////////////////////////////////////////////////////////
// h_exists
////////////////////////////////////////////////////////////////////////////////

val intro_exists (#a:_) (x:a) (p : a -> hprop) (m:hheap (p x))
  : Lemma (interp (h_exists p) m)

val elim_exists (#a:_) (p:a -> hprop) (q:hprop) (m:hheap (h_exists p))
  : Lemma
    ((forall (x:a). interp (p x) m ==> interp q m) ==>
     interp q m)


////////////////////////////////////////////////////////////////////////////////
// h_forall
////////////////////////////////////////////////////////////////////////////////

val intro_forall (#a:_) (p : a -> hprop) (m:heap)
  : Lemma ((forall x. interp (p x) m) ==> interp (h_forall p) m)

val elim_forall (#a:_) (p : a -> hprop) (m:hheap (h_forall p))
  : Lemma ((forall x. interp (p x) m) ==> interp (h_forall p) m)

////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////

val affine_star (p q:hprop) (m:heap)
  : Lemma
    (ensures (interp (p `star` q) m ==> interp p m /\ interp q m))

////////////////////////////////////////////////////////////////////////////////
// emp
////////////////////////////////////////////////////////////////////////////////
val intro_emp (m:heap)
  : Lemma (interp emp m)

val emp_unit (p:hprop)
  : Lemma ((p `star` emp) `equiv` p)

////////////////////////////////////////////////////////////////////////////////
// refinement
////////////////////////////////////////////////////////////////////////////////

let depends_only_on (q:heap -> prop) (fp: hprop) =
  (forall h0 h1. q h0 /\ disjoint h0 h1 ==> q (join h0 h1)) /\
  (forall (h0:hheap fp) (h1:heap{disjoint h0 h1}). q h0 <==> q (join h0 h1))

let fp_prop fp = p:(heap -> prop){p `depends_only_on` fp}

val weaken_depends_only_on (q:heap -> prop) (fp fp': hprop)
  : Lemma (depends_only_on q fp ==> depends_only_on q (fp `star` fp'))

val refine (p:hprop) (q:fp_prop p) : hprop

val refine_equiv (p:hprop) (q:fp_prop p) (h:heap)
  : Lemma (interp p h /\ q h <==> interp (refine p q) h)

val refine_star (p0 p1:hprop) (q:fp_prop p0)
  : Lemma (weaken_depends_only_on q p0 p1;
           equiv (refine (p0 `star` p1) q) (refine p0 q `star` p1))

val interp_depends_only (p:hprop)
  : Lemma (interp p `depends_only_on` p)

////////////////////////////////////////////////////////////////////////////////
// Memory
////////////////////////////////////////////////////////////////////////////////
val mem : Type u#1
val locks_invariant : mem -> hprop

val heap_of_mem (x:mem) : heap

val m_disjoint: mem -> heap -> prop

val upd_joined_heap: (m:mem) -> (h:heap{m_disjoint m h}) -> mem

let hmem (fp:hprop) = m:mem{interp (fp `star` locks_invariant m) (heap_of_mem m)}

////////////////////////////////////////////////////////////////////////////////
// Actions:
// sel, split, update
////////////////////////////////////////////////////////////////////////////////
let pre_action (fp:hprop) (a:Type) (fp':a -> hprop) =
  hheap fp -> (x:a & hheap (fp' x))

let is_frame_preserving #a #fp #fp' (f:pre_action fp a fp') =
  forall frame h0.
    interp (fp `star` frame) h0 ==>
    (let (| x, h1 |) = f h0 in
     interp (fp' x `star` frame) h1)

let action_depends_only_on_fp (#pre:_) (#a:_) (#post:_) (f:pre_action pre a post)
  = forall (h0:hheap pre)
      (h1:heap {disjoint h0 h1})
      (post: (x:a -> fp_prop (post x))).
      (interp pre (join h0 h1) /\ (
       let (| x0, h |) = f h0 in
       let (| x1, h' |) = f (join h0 h1) in
       x0 == x1 /\
       (post x0 h <==> post x1 h')))

let action (fp:hprop) (a:Type) (fp':a -> hprop) =
  f:pre_action fp a fp'{ is_frame_preserving f /\
                         action_depends_only_on_fp f }


let pre_m_action (fp:hprop) (a:Type) (fp':a -> hprop) =
  hmem fp -> (x:a & hmem (fp' x))

val m_action_depends_only_on (#pre:hprop) (#a:Type) (#post:a -> hprop) (f:pre_m_action pre a post) : prop

val is_m_frame_preserving (#a:Type) (#fp:hprop) (#fp':a -> hprop) (f:pre_m_action fp a fp') : prop

let m_action (fp:hprop) (a:Type) (fp':a -> hprop) =
  f:pre_m_action fp a fp'{ is_m_frame_preserving f /\ m_action_depends_only_on f }

val frame_fp_prop (#fp:_) (#a:Type) (#fp':_) (act:action fp a fp')
                  (#frame:hprop) (q:fp_prop frame)
   : Lemma (forall (h0:hheap (fp `star` frame)).
              (affine_star fp frame h0;
               q h0 ==>
               (let (| x, h1 |) = act h0 in
                q h1)))

val sel (#a:_) (r:ref a) (m:hheap (ptr r))
  : a

/// sel respect pts_to
val sel_lemma (#a:_) (r:ref a) (p:permission) (m:hheap (ptr_perm r p))
  : Lemma (interp (ptr r) m /\
           interp (pts_to r p (sel r m)) m)

/// memories satisfying [p1 `star` p2] can be split
/// into disjoint fragments satisfying each of them
val split_mem (p1 p2:hprop) (m:hheap (p1 `star` p2))
  : Tot (ms:(hheap p1 & hheap p2){
            let m1, m2 = ms in
            disjoint m1 m2 /\
            m == join m1 m2})

/// upd requires a full permission
val upd (#a:_) (r:ref a) (v:a)
  : m_action (ptr_perm r full_permission) unit (fun _ -> pts_to r full_permission v)

val alloc (#a:_) (v:a)
  : m_action emp (ref a) (fun x -> pts_to x full_permission v)

val lock (p:hprop) : Type0

val new_lock (p:hprop)
  : m_action p (lock p) (fun _ -> emp)
