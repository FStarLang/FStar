(*
   Copyright 2020 Microsoft Research

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
module U32 = FStar.UInt32
module S = FStar.Set
module U = FStar.Universe

let trivial_preorder (a: Type u#a) : Preorder.preorder a = fun _ _ -> True

[@@erasable]
noeq type perm : Type u#a =
  | MkPerm: v:real -> perm

let readable (p: perm) : GTot bool =
  MkPerm?.v p >. 0.0R

let writeable (p: perm) : GTot bool =
  MkPerm?.v p = 1.0R

let half_perm (p: perm) : GTot (perm) =
  MkPerm ((MkPerm?.v p) /. two)

let sum_perm (p1 p2: perm u#a) : GTot (perm u#a) =
  MkPerm (MkPerm?.v p1 +.  MkPerm?.v p2)

let lesser_equal_perm (p1 p2:perm u#a) : GTot bool =
  MkPerm?.v p1 <=.  MkPerm?.v p2

let full_perm : perm = MkPerm 1.0R

/// Abstract type of addresses

val addr: eqtype

/// A memory maps a reference to its associated value

val array_ref (a: Type u#a) : Type u#0

val length (#t: Type) (a: array_ref t) : GTot (n:U32.t)

val offset (#t: Type) (a: array_ref t)
    : GTot (n:U32.t{U32.v n + U32.v (length a) <= UInt.max_int 32})

val max_length (#t: Type) (a: array_ref t)
    : GTot (n: U32.t{U32.v (offset a) + U32.v (length a) <= U32.v n})

let is_null_array (#t: Type) (a:array_ref t) : GTot bool =
  length a = 0ul

val address (#t: Type) (a: array_ref t{not (is_null_array a)}) : GTot addr

let freeable (#t: Type) (a: array_ref t) =
  not (is_null_array a) /\ offset a = 0ul /\ length a = max_length a

val reference (t: Type) (pre: Preorder.preorder t) : Type0

val ref_address (#t: Type)(#pre: Preorder.preorder t) (r: reference t pre) : GTot addr

/// The type of mem assertions

[@@erasable]
val hprop : Type u#(a + 1)

/// Type of mem

val mem : Type u#(a + 1)

val core_mem (m:mem u#a) : mem u#a

/// A predicate describing non-overlapping memories

val disjoint (m0 m1:mem u#a) : prop

/// disjointness is symmetric

val disjoint_sym (m0 m1:mem u#a)
: Lemma (disjoint m0 m1 <==> disjoint m1 m0)

/// disjoint memories can be combined

val join (m0:mem u#a) (m1:mem u#a{disjoint m0 m1}) : mem u#a

/// disjointness distributes over join

val disjoint_join (m0 m1 m2:mem u#a)
    : Lemma (
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2) ==>
      disjoint m0 m1 /\
      disjoint m0 m2 /\
      disjoint (join m0 m1) m2 /\
      disjoint (join m0 m2) m1)

val join_commutative (m0 m1:mem u#a)
    : Lemma
      (requires disjoint m0 m1)
      (ensures (disjoint_sym m0 m1; join m0 m1 == join m1 m0))

val join_associative (m0 m1 m2:mem u#a)
    : Lemma
      (requires disjoint m1 m2 /\ disjoint m0 (join m1 m2))
      (ensures (disjoint_join m0 m1 m2; join m0 (join m1 m2) == join (join m0 m1) m2))

////////////////////////////////////////////////////////////////////////////////
// HProp
////////////////////////////////////////////////////////////////////////////////


/// interpreting mem assertions as memory predicates

val interp (p:hprop u#a) (m:mem u#a) : prop


/// Equivalence relation on hprops is just
/// equivalence of their interpretations

let equiv (p1 p2:hprop u#a) : prop =
  forall m. interp p1 m <==> interp p2 m

/// All the standard connectives of separation logic

val emp : hprop u#a

val pts_to_array
      (#t: Type u#a)
      (a:array_ref t)
      (p:perm u#a{readable p})
      (contents:Ghost.erased (Seq.lseq t (U32.v (length a))))
    : hprop u#a

val pts_to_ref_with_liveness
      (#t: Type u#a)
      (#pre: Preorder.preorder t)
      (r: reference t pre)
      (p:perm u#a{readable p})
      (contents: Ghost.erased t)
      (live: U.raise_t u#0 u#a bool)
    : hprop u#a

val h_and (p1 p2:hprop u#a) : hprop u#a

val h_or  (p1 p2:hprop u#a) : hprop u#a

val star  (p1 p2:hprop u#a) : hprop u#a

val wand  (p1 p2:hprop u#a) : hprop u#a

val h_exists (#a:Type u#a) (f: (a -> hprop u#a)) : hprop u#a

val h_forall (#a:Type u#a) (f: (a -> hprop u#a)) : hprop u#a

type hmem (p:hprop u#a) = m:mem u#a{interp p m}

////////////////////////////////////////////////////////////////////////////////
//properties of equiv
////////////////////////////////////////////////////////////////////////////////

val equiv_symmetric (p1 p2:hprop u#a)
    : Lemma (p1 `equiv` p2 ==> p2 `equiv` p1)

val equiv_extensional_on_star (p1 p2 p3:hprop u#a)
    : Lemma (p1 `equiv` p2 ==> (p1 `star` p3) `equiv` (p2 `star` p3))

////////////////////////////////////////////////////////////////////////////////
// pts_to_array and abbreviations
////////////////////////////////////////////////////////////////////////////////

let array_perm (#t: Type u#a) (a: array_ref t) (p:perm u#a{readable p}) =
  h_exists u#a (pts_to_array a p)

let array (#t: Type u#a) (a: array_ref t) =
  h_exists u#a (fun (p:perm u#a{readable p}) -> array_perm u#a a p)

val pts_to_array_injective
      (#t: Type u#a)
      (a: array_ref t{not (is_null_array a)})
      (p:perm u#a{readable p})
      (c0 c1: Seq.lseq t (U32.v (length a)))
      (m:mem u#a)
    : Lemma
      (requires (
        interp (pts_to_array a p c0) m /\
        interp (pts_to_array a p c1) m))
      (ensures (c0 == c1))

val share_pts_to_array
      (#t: Type u#a)
      (a: array_ref t{not (is_null_array a)})
      (p:perm u#a{readable p})
      (v:Seq.lseq t (U32.v (length a)))
      (m:mem u#a)
    : Lemma
      (requires interp (pts_to_array a p v) m)
      (ensures interp (pts_to_array a (half_perm p) v `star` pts_to_array a (half_perm p) v) m)

val gather_pts_to_array
      (#t: Type u#a)
      (a: array_ref t{not (is_null_array a)})
      (p0:perm u#a{readable p0})
      (p1:perm u#a{readable p1})
      (v0 v1: Seq.lseq t (U32.v (length a)))
      (m:mem u#a)
    : Lemma
      (requires interp (pts_to_array a p0 v0 `star` pts_to_array a p1 v1) m)
      (ensures interp (pts_to_array a (sum_perm p0 p1) v0) m)

////////////////////////////////////////////////////////////////////////////////
// pts_to_ref and abbreviations
////////////////////////////////////////////////////////////////////////////////

let pts_to_ref
      (#t: Type u#a)
      (#pre: Preorder.preorder t)
      (r: reference t pre)
      (p:perm u#a{readable p})
      (contents: Ghost.erased t)
    : hprop u#a
    =
  pts_to_ref_with_liveness r p contents (U.raise_val u#0 u#a true)

let pts_to_ref_or_dead
      (#t: Type u#a)
      (#pre: Preorder.preorder t)
      (r: reference t pre)
      (p:perm u#a{readable p})
      (contents: Ghost.erased t)
    : hprop u#a
    =
  h_exists (pts_to_ref_with_liveness r p contents)

let ref_perm
      (#t: Type u#a)
      (#pre: Preorder.preorder t)
      (r: reference t pre)
      (p:perm u#a{readable p})
    : hprop u#a
    =
  h_exists (pts_to_ref r p)

let ref_perm_or_dead
      (#t: Type u#a)
      (#pre: Preorder.preorder t)
      (r: reference t pre)
      (p:perm u#a{readable p})
    : hprop u#a
    =
  h_exists (pts_to_ref_or_dead r p)

let ref (#t: Type) (#pre: Preorder.preorder t)(r: reference t pre) : hprop u#a =
  h_exists (fun (p:perm u#a{readable p}) -> ref_perm r p)

let ref_or_dead (#t: Type u#a) (#pre: Preorder.preorder t)(r: reference t pre) : hprop u#a =
  h_exists (fun (p:perm u#a{readable p}) -> ref_perm_or_dead r p)

val pts_to_ref_injective
      (#t: Type u#a)
      (#pre: Preorder.preorder t)
      (a: reference t pre)
      (p0:perm u#a{readable p0})
      (p1:perm u#a{readable p1})
      (c0 c1: t)
      (m:mem u#a)
    : Lemma
      (requires (
        interp (pts_to_ref a p0 c0) m /\
        interp (pts_to_ref a p1 c1) m))
      (ensures (c0 == c1))

val share_pts_to_ref
      (#t: Type u#a)
      (#pre:Preorder.preorder t)
      (r: reference t pre)
      (p:perm u#a{readable p})
      (v:t)
      (m:mem u#a)
    : Lemma
      (requires interp (pts_to_ref r p v) m)
      (ensures interp (pts_to_ref r (half_perm p) v `star` pts_to_ref r (half_perm p) v) m)

val gather_pts_to_ref
      (#t: Type u#a)
      (#pre:Preorder.preorder t)
      (r: reference t pre)
      (p0:perm u#a{readable p0})
      (p1:perm u#a{readable p1})
      (v0 v1: t)
      (m:mem u#a)
    : Lemma
      (requires interp (pts_to_ref r p0 v0 `star` pts_to_ref r p1 v1) m)
      (ensures interp (pts_to_ref r (sum_perm p0 p1) v0) m)

////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////

val intro_star (p q:hprop u#a) (mp:hmem p) (mq:hmem q)
    : Lemma
      (requires disjoint mp mq)
      (ensures interp (p `star` q) (join mp mq))

val star_commutative (p1 p2:hprop u#a)
    : Lemma ((p1 `star` p2) `equiv` (p2 `star` p1))

val star_associative (p1 p2 p3:hprop u#a)
    : Lemma ((p1 `star` (p2 `star` p3)) `equiv` ((p1 `star` p2) `star` p3))

val star_congruence (p1 p2 p3 p4:hprop u#a)
    : Lemma
      (requires p1 `equiv` p3 /\ p2 `equiv` p4)
      (ensures (p1 `star` p2) `equiv` (p3 `star` p4))

////////////////////////////////////////////////////////////////////////////////
// wand
////////////////////////////////////////////////////////////////////////////////

/// A low-level introduction form for wand in terms of disjoint
val intro_wand_alt (p1 p2:hprop u#a) (m:mem u#a)
    : Lemma
      (requires (forall (m0:hmem p1). disjoint m0 m ==> interp p2 (join m0 m)))
      (ensures interp (wand p1 p2) m)

/// A higher-level introduction for wand as a cut
val intro_wand (p q r:hprop u#a) (m:hmem q)
    : Lemma
      (requires (forall (m:hmem (p `star` q)). interp r m))
      (ensures interp (p `wand` r) m)

/// Standard wand elimination
val elim_wand (p1 p2:hprop u#a) (m:mem u#a)
    : Lemma
      (requires (interp ((p1 `wand` p2) `star` p1) m))
      (ensures interp p2 m)

////////////////////////////////////////////////////////////////////////////////
// or
////////////////////////////////////////////////////////////////////////////////
val intro_or_l (p1 p2:hprop u#æ) (m:hmem p1)
    : Lemma (interp (h_or p1 p2) m)

val intro_or_r (p1 p2:hprop u#a) (m:hmem p2)
    : Lemma (interp (h_or p1 p2) m)

/// star can be factored out of or
val or_star (p1 p2 p:hprop u#a) (m:hmem ((p1 `star` p) `h_or` (p2 `star` p)))
    : Lemma (interp ((p1 `h_or` p2) `star` p) m)

/// A standard or eliminator
val elim_or (p1 p2 q:hprop u#a) (m:hmem (p1 `h_or` p2))
    : Lemma (((forall (m:hmem p1). interp q m) /\
              (forall (m:hmem p2). interp q m)) ==> interp q m)

////////////////////////////////////////////////////////////////////////////////
// and
////////////////////////////////////////////////////////////////////////////////
val intro_and (p1 p2:hprop u#a) (m:mem u#a)
    : Lemma (interp p1 m /\ interp p2 m ==> interp (p1 `h_and` p2) m)

val elim_and (p1 p2:hprop u#a) (m:hmem (p1 `h_and` p2))
    : Lemma (interp p1 m /\ interp p2 m)

////////////////////////////////////////////////////////////////////////////////
// h_exists
////////////////////////////////////////////////////////////////////////////////

val intro_exists (#t: Type u#a) (x:t) (p : t -> hprop u#a) (m:hmem (p x))
    : Lemma (interp (h_exists p) m)

val elim_exists (#t: Type u#a) (p:t -> hprop u#a) (q:hprop u#a) (m:hmem (h_exists u#a p))
    : Lemma ((forall (x:t). interp (p x) m ==> interp q m) ==> interp q m)

val h_exists_extensionality (#t:Type u#a) (p q:t -> hprop u#a)
    : Lemma
      (requires forall (x:t). p x `equiv` q x)
      (ensures h_exists p `equiv` h_exists q)

////////////////////////////////////////////////////////////////////////////////
// h_forall
////////////////////////////////////////////////////////////////////////////////

val intro_forall (#t:Type u#a) (p : t -> hprop u#a) (m:mem u#a)
    : Lemma ((forall x. interp (p x) m) ==> interp (h_forall p) m)

val elim_forall (#t: Type u#a) (p : t -> hprop u#a) (m:hmem (h_forall u#a p))
    : Lemma ((forall x. interp (p x) m) ==> interp (h_forall p) m)

////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////

val affine_star (p q:hprop u#a) (m:mem u#a)
    : Lemma ((interp (p `star` q) m ==> interp p m /\ interp q m))

////////////////////////////////////////////////////////////////////////////////
// emp
////////////////////////////////////////////////////////////////////////////////
val intro_emp (m:mem u#a) : Lemma (interp emp m)

val emp_unit (p:hprop u#a) : Lemma ((p `star` emp) `equiv` p)

////////////////////////////////////////////////////////////////////////////////
// refinement
////////////////////////////////////////////////////////////////////////////////

let refine_mprop_depends_only_on (q:mem u#a -> prop) (fp: hprop u#a) =
  (forall h0 h1. q h0 /\ disjoint h0 h1 ==> q (join h0 h1)) /\
  (forall (h0:hmem fp) (h1:mem u#a{disjoint h0 h1}). q h0 <==> q (join h0 h1)) /\
  (forall m. q m == q (core_mem m))

let refine_mprop (fp: hprop u#a) = p:(mem u#a -> prop){p `refine_mprop_depends_only_on` fp}

val weaken_refine_mprop_depends_only_on (q:mem u#a -> prop) (fp fp': hprop u#a)
    : Lemma (refine_mprop_depends_only_on q fp ==> refine_mprop_depends_only_on q (fp `star` fp'))

val refine (p:hprop u#a) (q:refine_mprop p) : hprop u#a

val refine_equiv (p:hprop u#a) (q:refine_mprop p) (h:mem u#a)
    : Lemma (interp p h /\ q h <==> interp (refine p q) h)

val refine_star (p0 p1:hprop u#a) (q:refine_mprop p0)
    : Lemma (
      weaken_refine_mprop_depends_only_on q p0 p1;
      equiv (refine (p0 `star` p1) q) (refine p0 q `star` p1))

val lock_addr: eqtype

val locks_invariant : S.set lock_addr -> mem u#a -> hprop u#a

let hmem_with_inv' (e:S.set lock_addr) (fp:hprop u#a) =
  m:mem{interp (fp `star` locks_invariant e m) m}

let hmem_with_inv (fp:hprop u#a) = m:mem u#a{interp (fp `star` locks_invariant Set.empty m) m}

let mprop (hp:hprop u#a) =
  q:(mem u#a -> prop){
    forall (m0:mem{interp hp m0}) (m1:mem{disjoint m0 m1}). q m0 <==> q (join m0 m1)}


(***** Following lemmas are needed in Steel.Effect *****)

val core_mem_interp (hp:hprop u#a) (m:mem u#a)
    : Lemma
      (requires interp hp m)
      (ensures interp hp (core_mem m))
      [SMTPat (interp hp (core_mem m))]

val interp_depends_only_on (hp:hprop u#a)
    : Lemma
      (forall (m0:hmem hp) (m1:mem u#a{disjoint m0 m1}).
        interp hp m0 <==> interp hp (join m0 m1))

let affine_star_smt (p q:hprop u#a) (m:mem u#a)
    : Lemma (interp (p `star` q) m ==> interp p m /\ interp q m)
    [SMTPat (interp (p `star` q) m)]
    =
  affine_star p q m

val h_exists_cong (#a:Type) (p q : a -> hprop)
    : Lemma
      (requires (forall x. p x `equiv` q x))
      (ensures (h_exists p `equiv` h_exists q))
