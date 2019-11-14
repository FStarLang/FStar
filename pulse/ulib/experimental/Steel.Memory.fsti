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
let perm =
  r:FStar.Real.real{
    FStar.Real.(0.0R <. r && r <=. 1.0R)
  }

/// Abstract type of memories
val mem  : Type u#1

/// A memory maps a reference to its associated value
val ref (a:Type u#0) : Type u#0

/// A predicate describing non-overlapping memories
val disjoint (m0 m1:mem) : prop

/// disjointness is symmetric
val disjoint_sym (m0 m1:mem)
  : Lemma (disjoint m0 m1 <==> disjoint m1 m0)

/// disjoint memories can be combined
val join (m0:mem) (m1:mem{disjoint m0 m1}) : mem

/// disjointness distributes over join
val disjoint_join (m0 m1 m2:mem)
  : Lemma (disjoint m1 m2 /\
           disjoint m0 (join m1 m2) ==>
           disjoint m0 m1 /\
           disjoint m0 m2 /\
           disjoint (join m0 m1) m2 /\
           disjoint (join m0 m2) m1)

val join_commutative (m0 m1:mem)
  : Lemma
    (requires
      disjoint m0 m1)
    (ensures
      (disjoint_sym m0 m1;
       join m0 m1 == join m1 m0))

val join_associative (m0 m1 m2:mem)
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
val interp (p:hprop) (m:mem) : prop

/// A common abbreviation: memories validating p
let hmem (p:hprop) = m:mem{interp p m}

/// Equivalence relation on hprops is just
/// equivalence of their interpretations
let equiv (p1 p2:hprop) =
  forall m. interp p1 m <==> interp p2 m

/// All the standard connectives of separation logic
val emp : hprop
val pts_to (#a:_) (r:ref a) (p:perm) (v:a) : hprop
val h_and (p1 p2:hprop) : hprop
val h_or  (p1 p2:hprop) : hprop
val star  (p1 p2:hprop) : hprop
val wand  (p1 p2:hprop) : hprop
val h_exists (#a:Type0) (f: (a -> hprop)) : hprop
val h_forall (#a:Type0) (f: (a -> hprop)) : hprop

////////////////////////////////////////////////////////////////////////////////
// pts_to and abbreviations
//////////////////////////////////////////////////////////////////////////////////////////
let ptr_perm #a (r:ref a) (p:perm) =
    h_exists (fun v -> pts_to r p v)

let ptr #a (r:ref a) =
    h_exists (fun p -> ptr_perm r p)

////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////
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
// Actions:
// sel, split, update
////////////////////////////////////////////////////////////////////////////////
val sel (#a:_) (r:ref a) (m:hmem (ptr r))
  : a

/// sel respect pts_to
val sel_lemma (#a:_) (r:ref a) (p:perm) (m:hmem (ptr_perm r p))
  : Lemma (interp (ptr r) m /\
           interp (pts_to r p (sel r m)) m)

/// memories satisfying [p1 `star` p2] can be split
/// into disjoint fragments satisfying each of them
val split_mem (p1 p2:hprop) (m:hmem (p1 `star` p2))
  : Tot (ms:(hmem p1 & hmem p2){
            let m1, m2 = ms in
            disjoint m1 m2 /\
            m == join m1 m2})

/// upd requires a full permission
/// it respects frames
val upd (#a:_) (r:ref a) (v:a)
        (frame:hprop)
        (m:hmem (ptr_perm r 1.0R  `star` frame))
  : Tot (m:hmem (pts_to r 1.0R v `star` frame))

////////////////////////////////////////////////////////////////////////////////
// wand
////////////////////////////////////////////////////////////////////////////////

/// A low-level introduction form for wand in terms of disjoint
val intro_wand_alt (p1 p2:hprop) (m:mem)
  : Lemma
    (requires
      (forall (m0:hmem p1).
         disjoint m0 m ==>
         interp p2 (join m0 m)))
    (ensures
      interp (wand p1 p2) m)

/// A higher-level introduction for wand as a cut
val intro_wand (p q r:hprop) (m:hmem q)
  : Lemma
    (requires
      (forall (m:hmem (p `star` q)). interp r m))
    (ensures
      interp (p `wand` r) m)

/// Standard wand elimination
val elim_wand (p1 p2:hprop) (m:mem)
  : Lemma
    (requires
      (interp ((p1 `wand` p2) `star` p1) m))
    (ensures
      interp p2 m)

////////////////////////////////////////////////////////////////////////////////
// or
////////////////////////////////////////////////////////////////////////////////
val intro_or_l (p1 p2:hprop) (m:hmem p1)
  : Lemma (interp (h_or p1 p2) m)

val intro_or_r (p1 p2:hprop) (m:hmem p2)
  : Lemma (interp (h_or p1 p2) m)

/// star can be factored out of or
val or_star (p1 p2 p:hprop) (m:hmem ((p1 `star` p) `h_or` (p2 `star` p)))
  : Lemma (interp ((p1 `h_or` p2) `star` p) m)

/// A standard or eliminator
val elim_or (p1 p2 q:hprop) (m:hmem (p1 `h_or` p2))
  : Lemma (((forall (m:hmem p1). interp q m) /\
            (forall (m:hmem p2). interp q m)) ==> interp q m)


////////////////////////////////////////////////////////////////////////////////
// and
////////////////////////////////////////////////////////////////////////////////
val intro_and (p1 p2:hprop) (m:mem)
  : Lemma (interp p1 m /\
           interp p2 m ==>
           interp (p1 `h_and` p2) m)

val elim_and (p1 p2:hprop) (m:hmem (p1 `h_and` p2))
  : Lemma (interp p1 m /\
           interp p2 m)

////////////////////////////////////////////////////////////////////////////////
// h_exists
////////////////////////////////////////////////////////////////////////////////

val intro_exists (#a:_) (x:a) (p : a -> hprop) (m:hmem (p x))
  : Lemma (interp (h_exists p) m)

val elim_exists (#a:_) (p:a -> hprop) (q:hprop) (m:hmem (h_exists p))
  : Lemma
    ((forall (x:a). interp (p x) m ==> interp q m) ==>
     interp q m)


////////////////////////////////////////////////////////////////////////////////
// h_forall
////////////////////////////////////////////////////////////////////////////////

val intro_forall (#a:_) (p : a -> hprop) (m:mem)
  : Lemma ((forall x. interp (p x) m) ==> interp (h_forall p) m)

val elim_forall (#a:_) (p : a -> hprop) (m:hmem (h_forall p))
  : Lemma ((forall x. interp (p x) m) ==> interp (h_forall p) m)

////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////

val intro_star (p q:hprop) (mp:hmem p) (mq:hmem q)
  : Lemma
    (requires
      disjoint mp mq)
    (ensures
      interp (p `star` q) (join mp mq))

val affine_star (p q:hprop) (m:mem)
  : Lemma
    (ensures (interp (p `star` q) m ==> interp p m))

////////////////////////////////////////////////////////////////////////////////
// emp
////////////////////////////////////////////////////////////////////////////////
val intro_emp (m:mem)
  : Lemma (interp emp m)

val emp_unit (p:hprop)
  : Lemma ((p `star` emp) `equiv` p)

////////////////////////////////////////////////////////////////////////////////
// Allocation
////////////////////////////////////////////////////////////////////////////////
val t : Type u#1
val mem_of_t (x:t) : mem
val alloc (#a:_) (v:a) (frame:hprop) (tmem:t{interp frame (mem_of_t tmem)})
  : (x:ref a &
     tmem:t { interp (pts_to x 1.0R v `star` frame) (mem_of_t tmem)} )
