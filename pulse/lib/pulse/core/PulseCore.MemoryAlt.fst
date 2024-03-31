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
module PulseCore.MemoryAlt
open FStar.Ghost
open FStar.PCM
open PulseCore.Tags
module M_ = PulseCore.NondeterministicMonotonicStateMonad
module F = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality
module H0 = PulseCore.Heap
module H2 = PulseCore.TwoLevelHeap
module PP = PulseCore.Preorder
module MSTTotal = PulseCore.MonotonicStateMonad
module S = FStar.Set
module Frac = PulseCore.FractionalPermission
module L = FStar.List.Tot
module PA = PulseCore.PCM.Agreement

let istore : Type u#(a + 3) = erased (H0.heap u#(a + 2))

noeq
type iheap : Type u#(a + 3) = {
    concrete: H2.heap u#a; //contains both the concrete and ghost heaps; and a big heap and small heap
    invariants: istore u#a
}


noeq
type mem : Type u#(a + 3) =
  {
    ctr: nat;
    ghost_ctr: erased nat;
    iname_ctr: erased nat;
    iheap: iheap u#a;
  }

let empty_iheap = {
  concrete = H2.empty_heap;
  invariants = H0.empty_heap
}

let idisjoint (h0 h1:iheap u#a)
: prop
= H2.disjoint h0.concrete h1.concrete /\ H0.disjoint h0.invariants h1.invariants

let idisjoint_sym (h0 h1:iheap u#a)
: Lemma (idisjoint h0 h1 <==> idisjoint h1 h0)
        [SMTPat (idisjoint h0 h1)]
= ()

(** Disjoint heaps can be combined into a bigger heap*)
let ijoin (h0:iheap u#a) (h1:iheap u#a{idisjoint h0 h1})
: iheap u#a
= {
    concrete = H2.join h0.concrete h1.concrete;
    invariants = H0.join h0.invariants h1.invariants;
  }

let ijoin_commutative' (m0 m1:iheap)
  : Lemma
    (requires
      idisjoint m0 m1)
    (ensures
      ijoin m0 m1 == ijoin m1 m0)
    [SMTPat (ijoin m0 m1)]
  = H2.join_commutative m0.concrete m1.concrete;
    H0.join_commutative m0.invariants m1.invariants

(** The join operation is commutative *)
let ijoin_commutative (h0 h1:iheap u#a)
: Lemma
    (requires
      idisjoint h0 h1)
    (ensures
      (idisjoint h1 h0 /\
       ijoin h0 h1 == ijoin h1 h0))
= H2.join_commutative h0.concrete h1.concrete;
  H0.join_commutative h0.invariants h1.invariants


(** Disjointness distributes over join *)
let idisjoint_join (h0 h1 h2:iheap u#a)
: Lemma (idisjoint h1 h2 /\
         idisjoint h0 (ijoin h1 h2) ==>
           idisjoint h0 h1 /\
           idisjoint h0 h2 /\
           idisjoint (ijoin h0 h1) h2 /\
           idisjoint (ijoin h0 h2) h1)
= H2.disjoint_join h0.concrete h1.concrete h2.concrete;
  H0.disjoint_join h0.invariants h1.invariants h2.invariants

(** Join is associative *)
let ijoin_associative (h0 h1 h2:iheap u#a)
  : Lemma
    (requires
      idisjoint h1 h2 /\
      idisjoint h0 (ijoin h1 h2))
    (ensures
      (idisjoint h0 h1 /\
       idisjoint (ijoin h0 h1) h2 /\
       ijoin h0 (ijoin h1 h2) == ijoin (ijoin h0 h1) h2))
= H2.join_associative h0.concrete h1.concrete h2.concrete;
  H0.join_associative h0.invariants h1.invariants h2.invariants

let ijoin_associative2 (m0 m1 m2:iheap)
  : Lemma
    (requires
      idisjoint m0 m1 /\
      idisjoint (ijoin m0 m1) m2)
    (ensures
      idisjoint m1 m2 /\
      idisjoint m0 (ijoin m1 m2) /\
      ijoin m0 (ijoin m1 m2) == ijoin (ijoin m0 m1) m2)
    [SMTPat (ijoin (ijoin m0 m1) m2)]
  = idisjoint_join m2 m0 m1;
    ijoin_commutative m2 m1;
    ijoin_associative m0 m1 m2

let h2_join_empty (h:H2.heap)
  : Lemma (H2.disjoint h H2.empty_heap /\
           H2.join h H2.empty_heap == h)
           [SMTPatOr
              [[SMTPat (H2.disjoint h H2.empty_heap)];
               [SMTPat (H2.join h H2.empty_heap)]]]
  = H2.join_empty h

let h0_join_empty (h:H0.heap)
  : Lemma (H0.disjoint h H0.empty_heap /\
           H0.join h H0.empty_heap == h)
           [SMTPatOr
              [[SMTPat (H0.disjoint h H0.empty_heap)];
               [SMTPat (H0.join h H0.empty_heap)]]]
  = H0.join_empty h

let join_empty (h:iheap)
  : Lemma (idisjoint h empty_iheap)
  = ()

(**
  An affine heap proposition or affine heap predicate is a proposition whose validity does not
  change if the heap on which it is valid grows. In other terms, it is a proposition that is
  compatible with the disjoint/join operations for partial heaps. These affine heap predicates
  are the base of our separation logic.
*)
let heap_prop_is_affine (p:iheap -> prop) : prop =
  forall (h0 h1: iheap). p h0 /\ idisjoint h0 h1 ==> p (ijoin h0 h1)

(**
  An affine heap proposition
  *)
let a_heap_prop = p:(iheap -> prop) { heap_prop_is_affine p }


let is_ghost_action m0 m1 =
  H2.concrete m0.iheap.concrete == H2.concrete m1.iheap.concrete /\
  m0.ctr == m1.ctr

let ghost_action_preorder (_:unit)
  : Lemma (FStar.Preorder.preorder_rel is_ghost_action)
  = ()


let heap_of_mem (x:mem) : iheap = x.iheap

let mem_of_heap (h:iheap) : mem = {
  ctr = 0;
  ghost_ctr = 0;
  iname_ctr = 0;
  iheap = h;
}
let core_mem (m:mem) : mem = mem_of_heap (heap_of_mem m)

val core_mem_invol (m: mem u#a) : Lemma
  (core_mem (core_mem m) == core_mem m)
  [SMTPat (core_mem (core_mem m))]
let core_mem_invol m = ()

(**
  [slprop] is an abstract "separation logic proposition"

  The [erasable] attribute says that it is computationally irrelevant
  and will be extracted to [()]
*)
[@@erasable]
let slprop
: Type u#(a + 3)
= p:(iheap u#a ^-> prop) { heap_prop_is_affine p }

 
(** A predicate describing non-overlapping memories. *)
let disjoint (m0 m1:mem u#h)
  : prop
  = m0.ctr == m1.ctr /\
    m0.ghost_ctr == m1.ghost_ctr /\
    m0.iname_ctr == m1.iname_ctr /\
    idisjoint m0.iheap m1.iheap

(** Disjointness is symmetric *)
let disjoint_sym (m0 m1:mem u#h)
  : Lemma (disjoint m0 m1 <==> disjoint m1 m0)
          [SMTPat (disjoint m0 m1)]
  = ()

(** Disjoint memories can be combined. Based on [Steel.Heap.join] *)
let join (m0:mem u#h) (m1:mem u#h{disjoint m0 m1}) : mem u#h
= {
  ctr = m0.ctr;
  ghost_ctr = m0.ghost_ctr;
  iname_ctr = m0.iname_ctr;
  iheap = ijoin m0.iheap m1.iheap;
  }

(** Join is commutative *)
let join_commutative (m0 m1:mem)
  : Lemma
    (requires
      disjoint m0 m1)
    (ensures
      (disjoint m0 m1 /\
       disjoint m1 m0 /\
       join m0 m1 == join m1 m0))
  = ()

(** Disjointness distributes over join *)
let disjoint_join (m0 m1 m2:mem)
  : Lemma (disjoint m1 m2 /\
           disjoint m0 (join m1 m2) ==>
           disjoint m0 m1 /\
           disjoint m0 m2 /\
           disjoint (join m0 m1) m2 /\
           disjoint (join m0 m2) m1)
  = idisjoint_join m0.iheap m1.iheap m2.iheap

(** Join is associative *)
let join_associative (m0 m1 m2:mem)
  : Lemma
    (requires
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2))
    (ensures
      (disjoint_join m0 m1 m2;
       join m0 (join m1 m2) == join (join m0 m1) m2))
  = ijoin_associative m0.iheap m1.iheap m2.iheap

let big_slprop = H2.slprop u#a
let down_p (p:slprop u#a)
: H2.heap u#a -> prop
= fun h -> p { concrete = h; invariants = H0.empty_heap }
let down_p_affine (p:slprop) : Lemma (H2.heap_prop_is_affine (down_p p)) = 
  introduce forall (h1 h2:H2.heap).
          down_p p h1 /\ H2.disjoint h1 h2 ==> down_p p (H2.join h1 h2)
  with introduce _ ==> _
  with _ . (
    assert (down_p p h1);
    let h1_ = { concrete = h1; invariants = H0.empty_heap } in
    let h2_ = { concrete = h2; invariants = H0.empty_heap } in
    let h12 = H2.join h1 h2 in
    let h12_ = {concrete = H2.join h1 h2; invariants = H0.empty_heap} in
    assert (idisjoint h1_ h2_);
    ()
  )

let down (p:slprop u#a) : big_slprop =
  down_p_affine p;
  H2.as_slprop (down_p p)
let up_p (p:big_slprop) : iheap -> prop = fun h -> H2.interp p h.concrete
let up_p_affine (p:big_slprop)
: Lemma (heap_prop_is_affine (up_p p))
= H2.interp_depends_only_on p

let up (p:big_slprop) : slprop = up_p_affine p; F.on _ (up_p p)

let down_up (p:big_slprop)
: Lemma (down (up p) == p)
        [SMTPat (down (up p))]
= down_p_affine (up p);
  up_p_affine p;
  introduce forall h.
    H2.interp (down (up p)) h <==> H2.interp p h
  with  (
    calc (<==>) {
      H2.interp (down (up p)) h;
    (<==>) {}
      down_p (up p) h;
    (<==>) {}
      down_p (F.on _ (up_p p)) h;
    (<==>) { () }
      H2.interp p h;
    };
    ()
  );
  H2.slprop_extensionality (down (up p)) p

let small_slprop = H2.small_slprop
let down2 (s:slprop) = H2.down (down s)
let up2 (s:small_slprop) = up (H2.up s)
let small_is_also_big (s:slprop) = ()
let interp p m = p m.iheap

let equiv p1 p2 = forall m. p1 m <==> p2 m
module FExt = FStar.FunctionalExtensionality
let slprop_extensionality p q =
  FStar.PredicateExtensionality.predicateExtensionality iheap p q

val reveal_equiv (p1 p2:slprop u#a) : Lemma
  (ensures (forall m. interp p1 m <==> interp p2 m) <==> p1 `equiv` p2)
  [SMTPat (p1 `equiv` p2)]
let reveal_equiv p q = 
  introduce (forall m. interp p m <==> interp q m) ==> p `equiv` q
  with _ . (
    introduce forall (h:iheap). p h <==> q h
    with (
      let m : mem = { ctr = 0; ghost_ctr=0; iheap = h; iname_ctr=0 } in
      assert (interp p m <==> interp q m)
    )
  )

let slprop_equiv_refl p = ()

let core_ref = H2.core_ref
let core_ref_null = H2.core_ref_null
let core_ref_is_null r = H2.core_ref_is_null r

let as_slprop (f:a_heap_prop) : slprop = F.on _ f

let emp : slprop u#a = up H2.emp
let pure p = up (H2.pure p)
let star p1 p2 =
  as_slprop (fun (h: iheap) ->
    exists (h1 h2 : iheap).
        h1 `idisjoint` h2 /\
        h == ijoin h1 h2 /\
        p1 h1 /\
        p2 h2)
let h_exists #a f =
  as_slprop (fun h -> exists (x:a). f x h)

let emp_unit p =
  introduce forall h. interp p h <==> interp (p `star` emp) h
  with (
    assert (h == join h ({h with iheap = empty_iheap}));
    H2.intro_emp empty_iheap.concrete
  )

let pure_equiv p q = H2.pure_equiv p q
val pure_interp (q:prop) (m:mem) 
  : Lemma (interp (pure q) m <==> q)
          [SMTPat (interp (pure q) m)]
let pure_interp q m = H2.pure_interp q (heap_of_mem m).concrete
let pure_true_emp () : Lemma (pure True `equiv` emp) =
  FStar.Classical.forall_intro (H2.pure_interp True);
  FStar.Classical.forall_intro H2.intro_emp;
  slprop_extensionality (pure True) emp


////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////
let star_commutative (p1 p2:slprop) = ()
let star_associative (p1 p2 p3:slprop) = ()

let star_congruence (p1 p2 p3 p4:slprop) =
  slprop_extensionality p1 p3;
  slprop_extensionality p2 p4

let iinterp_up_down (p:slprop) (h:iheap)
: Lemma (
    p { h with invariants = H0.empty_heap } <==>
    (up (down p)) h)
= calc (<==>) {
    (up (down p)) h;
      (<==>) {}
    up_p (down p) h;
      (<==>) {}
    H2.interp (down p) h.concrete;
      (<==>) {  }
    (down_p_affine p;
     H2.interp (H2.as_slprop (down_p p)) h.concrete);
      (<==>) {}
    down_p p h.concrete;
      (<==>) {}
    p { h with invariants = H0.empty_heap };
  }

let big_star_congruence (p1 p2:big_vprop u#a)
: Lemma (is_big (p1 `star` p2))
= introduce forall h. 
    (p1 `star` p2) h ==> (up (down (p1 `star` p2))) h
  with introduce _ ==> _ 
  with _. (
    eliminate exists h1 h2. 
      idisjoint h1 h2 /\
      h == ijoin h1 h2 /\
      p1 h1 /\
      p2 h2
    returns (up (down (p1 `star` p2))) h
    with _ . (
      iinterp_up_down (p1 `star` p2) h;
      let hh = { h with invariants = H0.empty_heap } in
      let hh1 = {h1 with invariants = H0.empty_heap} in
      let hh2 = {h2 with invariants = H0.empty_heap} in
      assert (p1 hh1);
      assert (p2 hh2);
      assert (idisjoint hh1 hh2);
      assert ((p1 `star` p2) hh)
    )
  );
  introduce forall h. 
     (up (down (p1 `star` p2))) h ==> (p1 `star` p2) h
  with introduce _ ==> _
  with _. (
    iinterp_up_down (p1 `star` p2) h;
    let hh = { h with invariants = H0.empty_heap } in
    assert ((p1 `star` p2) hh);
    eliminate exists hh0 hh1. 
      idisjoint hh0 hh1 /\
      hh == ijoin hh0 hh1 /\
      p1 hh0 /\
      p2 hh1
    returns (p1 `star` p2) h
    with _ . (
      assert (reveal hh.invariants == H0.empty_heap);
      assert (H0.disjoint hh.invariants h.invariants);
      h0_join_empty h.invariants;
      H0.join_commutative hh.invariants h.invariants;
      let h0 = {hh0 with invariants = h.invariants} in
      let h1 = {hh1 with invariants = H0.empty_heap} in
      assert (H0.join hh.invariants h.invariants == reveal h.invariants);
      assert (ijoin h0 h1 == h);
      assert (p1 h0);
      assert (p2 h1)
    )
  );
  slprop_extensionality (up (down (p1 `star` p2))) (p1 `star` p2)

let big_exists_congruence (#a:Type u#a) (p:a -> slprop u#b)
: Lemma
    (requires forall x. is_big (p x))
    (ensures is_big (h_exists p))
= introduce forall h.
     (h_exists p) h ==> (up (down (h_exists p))) h
  with introduce _ ==> _
  with _ . (
    iinterp_up_down (h_exists p) h;
    eliminate exists x.
       (p x) h
    returns (up (down (h_exists p))) h
    with _ . (
      iinterp_up_down (p x) h
    )
  );
  introduce forall h.
    (up (down (h_exists p))) h ==> (h_exists p) h
  with introduce _ ==> _ 
  with _ . (
    iinterp_up_down (h_exists p) h;
    eliminate exists x.
      (up (down (p x))) h
    returns (h_exists p) h
    with _ . (
      iinterp_up_down (p x) h
    )
  );
  slprop_extensionality (h_exists p) (up (down (h_exists p)));
  ()
#restart-solver

let big_up_star (p q:H2.slprop)
: Lemma (up (p `H2.star` q) == (up p `star` up q))
        [SMTPat (up (p `H2.star` q))]
= introduce forall h.
      up (p `H2.star` q) h ==>
      (up p `star` up q) h
  with introduce _ ==> _
  with _ . (
    H2.elim_star p q h.concrete;
    eliminate exists h1 h2.
      H2.disjoint h1 h2 /\
      h.concrete == H2.join h1 h2 /\
      H2.interp p h1 /\
      H2.interp q h2
    returns (up p `star` up q) h
    with _ . (
      let hl = { h with concrete = h1 } in
      let hr = { concrete = h2; invariants = H0.empty_heap } in
      assert (idisjoint hl hr)
    )
  );
  introduce forall h.
      (up p `star` up q) h ==>
      up (p `H2.star` q) h
  with introduce _ ==> _
  with _ . (
    eliminate exists h1 h2.
      idisjoint h1 h2 /\
      h == ijoin h1 h2 /\
      up p h1 /\
      up q h2
    returns up (p `H2.star` q) h
    with _ . (
      H2.intro_star p q h1.concrete h2.concrete
      )    
  );
  slprop_extensionality (up (p `H2.star` q)) (up p `star` up q)

let down_star (p1 p2:big_vprop)
: Lemma 
  (ensures down (p1 `star` p2) == down p1 `H2.star` down p2)
= introduce forall h. 
    H2.interp (down (p1 `star` p2)) h ==>
    H2.interp (down p1 `H2.star` down p2) h
  with introduce _ ==> _
  with _ . (
    down_p_affine (p1 `star` p2);
    assert ((down_p (p1 `star` p2)) h);
    eliminate exists h1 h2. 
      H2.disjoint h1 h2 /\
      h == H2.join h1 h2 /\
      p1 { concrete = h1 ; invariants = H0.empty_heap } /\
      p2 { concrete = h2 ; invariants = H0.empty_heap }
    returns H2.interp (down p1 `H2.star` down p2) h
    with _ . (
      H2.intro_star (down p1) (down p2) h1 h2
    )
  );
  introduce forall h. 
    H2.interp (down p1 `H2.star` down p2) h ==>
    H2.interp (down (p1 `star` p2)) h
  with introduce _ ==> _
  with _ . (
    H2.elim_star (down p1) (down p2) h;
    eliminate exists h1 h2.
      H2.disjoint h1 h2 /\
      h == H2.join h1 h2 /\
      H2.interp (down p1) h1 /\
      H2.interp (down p2) h2
    returns
      H2.interp (down (p1 `star` p2)) h
    with _ . (
      down_p_affine (p1 `star` p2);
      assert (down (p1 `star` p2) == H2.as_slprop (down_p (p1 `star` p2)));
      let m1 = {concrete=h1; invariants=H0.empty_heap} in
      let m2 = {concrete=h2; invariants=H0.empty_heap} in
      assert (p1 m1 /\ p2 m2 /\ idisjoint m1 m2);
      assert (down_p (p1 `star` p2) h)
    )
  );
  H2.slprop_extensionality (down (p1 `star` p2)) (down p1 `H2.star` down p2)

let down_exists #a (p: a -> slprop)
: Lemma 
  (requires forall x. is_big (p x))
  (ensures down (h_exists p) == H2.h_exists (fun x -> down (p x)))
= introduce forall h.
      H2.interp (down (h_exists p)) h ==>
      H2.interp (H2.h_exists (fun x -> down (p x))) h
  with introduce _ ==> _
  with _ . (
    down_p_affine (h_exists p);
    assert (down_p (h_exists p) h);
    eliminate exists x.
      (p x) { concrete=h; invariants=H0.empty_heap }
    returns H2.interp (H2.h_exists (fun x -> down (p x))) h
    with _ . (
      down_p_affine (p x);
      H2.intro_h_exists  x (fun x -> down (p x)) h
    )
  );
  introduce forall h.
      H2.interp (H2.h_exists (fun x -> down (p x))) h ==>
      H2.interp (down (h_exists p)) h
  with introduce _ ==> _
  with _ . (
    H2.elim_h_exists (fun x -> down (p x)) h;
    down_p_affine (h_exists p)
  );
  H2.slprop_extensionality
    (down (h_exists p))
    (H2.h_exists (fun x -> down (p x)))

let small_star_congruence (p1 p2:vprop u#a)
: Lemma (is_small (p1 `star` p2))
= big_star_congruence p1 p2;
  assert (is_big (p1 `star` p2));
  down_star p1 p2;
  H2.vprop_star (down p1) (down p2)

module T = FStar.Tactics
let small_exists_congruence (#a:Type u#a) (p:a -> slprop u#b)
: Lemma
    (requires forall x. is_small (p x))
    (ensures is_small (h_exists p))
= big_exists_congruence #a p;
  assert (is_big (h_exists p));
  down_exists p;
  assert (forall x. H2.is_small (down (p x)));
  assert (H2.is_small (H2.h_exists (fun x -> (down (p x)))))
    by  (T.mapply (`H2.vprop_exists));
  assert (H2.is_small (down (h_exists p)))
  
let h_exists_equiv (#a:Type) (p q : a -> slprop)
: Lemma
    (requires (forall x. p x `equiv` q x))
    (ensures (h_exists p == h_exists q))
= slprop_extensionality (h_exists p) (h_exists q)

val affine_star (p q:slprop) (m:mem)
  : Lemma ((interp (p `star` q) m ==> interp p m /\ interp q m))

let affine_star (p q:slprop) (m:mem) = ()

let lift_h0_pred (pre:H0.heap -> prop)
  : iheap -> prop
  = fun h -> pre h.invariants

let h0_of_slprop (p:H0.slprop u#(a + 2)) : H0.a_heap_prop u#(a + 2) =
  H0.interp_depends_only_on p;
  fun h -> H0.interp p h

let lift_h0 (p:H0.slprop u#(a + 2))
: slprop u#a
= as_slprop (fun h -> h0_of_slprop p h.invariants)

let star_congruence_h0 (p q:H0.slprop)
: Lemma (lift_h0 (p `H0.star` q) == lift_h0 p `star` lift_h0 q)
= introduce forall h.
    (lift_h0 (p `H0.star` q)) h ==>
    (lift_h0 p `star` lift_h0 q) h
  with introduce _ ==> _
  with _ . (
    assert (H0.interp (p `H0.star` q) h.invariants);
    H0.elim_star p q h.invariants;
    eliminate exists h1 h2.
      H0.disjoint h1 h2 /\
      reveal h.invariants == H0.join h1 h2 /\
      H0.interp p h1 /\
      H0.interp q h2
    returns (lift_h0 p `star` lift_h0 q) h
    with _ . (
      let hl = { h with invariants = h1 } in
      let hr = { concrete = H2.empty_heap; invariants = h2 } in
      assert (idisjoint hl hr)
    )
  );
  introduce forall h.
    (lift_h0 p `star` lift_h0 q) h ==>
    (lift_h0 (p `H0.star` q)) h
  with introduce _ ==> _
  with _ . (
    eliminate exists h0 h1.
      idisjoint h0 h1 /\
      h == ijoin h0 h1 /\
      lift_h0 p h0 /\
      lift_h0 q h1
    returns (lift_h0 (p `H0.star` q)) h
    with _ . (
      H0.intro_star p q h0.invariants h1.invariants
    )
  );
  slprop_extensionality (lift_h0 (p `H0.star` q)) (lift_h0 p `star` lift_h0 q)

////////////////////////////////////////////////////////////////////////////////
// Invariants
////////////////////////////////////////////////////////////////////////////////

let iname = nat
module W = FStar.Witnessed.Core
let sl_pure_imp (p:prop) (q: squash p -> slprop) : slprop =
  as_slprop (fun (h:iheap) -> p ==> q () h)

let cell_pred_pre (c:H0.cell) =
  let H0.Ref a pcm _ _ = c in
  a == PA.agreement H2.slprop /\
  pcm == PA.pcm_agreement #H2.slprop

let cell_pred_post (c:H0.cell) (_:squash (cell_pred_pre c)) =
  let H0.Ref _ _ _ v = c in
  let v : PA.agreement H2.slprop = v in
  match v with
  | None -> emp
  | Some p -> up p


let invariant_of_one_cell (addr:nat) (e:inames) (l:istore u#a) : slprop u#a =
  if addr `S.mem` e then emp
  else match H0.select addr l with
       | Some c -> 
         sl_pure_imp 
          (cell_pred_pre c)
          (cell_pred_post c)
       | _ -> emp

let rec istore_invariant
         (from:nat)
         (e:inames) 
         (l:istore u#a)
: slprop u#a
= invariant_of_one_cell from e l `star` 
  (if from = 0 then emp else istore_invariant (from - 1) e l)

let istore_evolves : FStar.Preorder.preorder istore =
  fun (l1 l2 : istore) ->
    forall addr. Some? (H0.select addr l1) ==> H0.select addr l1 == H0.select addr l2

let inames_in (e:inames) (l:istore) : prop = 
  forall i. Set.mem i e ==> Some? (H0.select i l)

let heap_ctr_valid (ctr:nat) (ghost_ctr:nat) (iname_ctr:nat) (h:iheap u#a) : prop =
    h.concrete `H2.free_above_addr CONCRETE` ctr /\
    h.concrete `H2.free_above_addr GHOST` ghost_ctr /\
    h.invariants `H0.free_above_addr` iname_ctr

let ctr_validity (ctr:nat) (ghost_ctr:nat) (iname_ctr:nat) (h:iheap) : slprop =
    pure (heap_ctr_valid ctr ghost_ctr iname_ctr h)


let inames_ok e m = inames_in e m.iheap.invariants

let inames_ok_empty m = ()

let mem_invariant (e:inames) (m:mem u#a) : slprop u#a =
   istore_invariant m.iname_ctr e m.iheap.invariants
   `star`
   ctr_validity m.ctr m.ghost_ctr m.iname_ctr (heap_of_mem m)

let full_mem_pred (m:mem) =
  H2.full_heap_pred m.iheap.concrete /\
  H0.full_heap_pred m.iheap.invariants

(** Memory refined with invariants and a footprint *)
let hmem_with_inv_except (e:inames) (fp:slprop u#a) =
  m:full_mem{inames_ok e m /\ interp (fp `star` mem_invariant e m) m}

(** Memory refined with just a footprint and no invariants  *)
let hmem_with_inv (fp:slprop u#a) = hmem_with_inv_except S.empty fp


let mem_evolves (m0 m1 : full_mem) =
    H2.heap_evolves (heap_of_mem m0).concrete (heap_of_mem m1).concrete /\
    m0.iname_ctr <= m1.iname_ctr /\
    istore_evolves m0.iheap.invariants m1.iheap.invariants

let frame_related_mems (fp0 fp1:slprop u#a) e (m0:hmem_with_inv_except e fp0) (m1:hmem_with_inv_except e fp1) =
    forall (frame:slprop u#a).
      interp ((fp0 `star` frame) `star` mem_invariant e m0) m0 ==>
      interp ((fp1 `star` frame) `star` mem_invariant e m1) m1 /\
      mem_evolves m0 m1

let iname_for_p (i:iname) (p:slprop) (m:istore) =
  match H0.select i m with
  | None -> False
  | Some cell ->
    let H0.Ref a pcm _ v = cell in
    a == PA.agreement H2.slprop /\
    pcm == PA.pcm_agreement #H2.slprop /\ (
    let v : PA.agreement H2.slprop = cell.v in
    match v with
    | None -> False
    | Some q -> up q == p
    )


let iname_ref = erased (H0.ref _ (PA.pcm_agreement #H2.slprop))
let iname_ref_pts_to (i:iname_ref) (p:slprop u#a) =
  lift_h0 (H0.pts_to #_ #(PA.pcm_agreement #(H2.slprop u#a)) i (Some (down p)))

let set_add (i:iname) (s:inames) = Set.union (Set.singleton i) s

let star_comm (p1 p2:slprop)
  : Lemma ((p1 `star` p2) == (p2 `star` p1))
  = star_commutative p1 p2;
    slprop_extensionality (p1 `star` p2) (p2 `star` p1)

let star_assoc (p q r:slprop)
  : Lemma (p `star` (q `star` r) == (p `star` q) `star` r)
  = star_associative p q r;
    slprop_extensionality (p `star` (q `star` r)) ((p `star` q) `star` r)

let emp_u (p:slprop)
: Lemma (p == p `star` emp /\ emp `star` p == p)
= emp_unit p;
  star_comm p emp;
  slprop_extensionality p (p `star` emp)

let pqr_qpr (p q r:slprop)
  : Lemma (p `star` (q `star` r) == q `star` (p `star` r))
  = calc (==) {
      p `star` (q `star` r);
    (==) { star_assoc p q r }
      (p `star` q) `star` r;
    (==) { star_comm p q }
      (q `star` p) `star` r;
    (==) { star_assoc q p r}
      q `star` (p `star` r);
  }

module T = FStar.Tactics

let rec weaken_inames_istore_invariant
          (from:nat)
          (e:inames)
          (e':inames { forall i. i `Set.mem` e' ==> from < i })
          (l:istore)
: Lemma
  (ensures istore_invariant from e l == istore_invariant from (Set.union e' e) l)
  (decreases from)
= if from = 0
  then ()
  else weaken_inames_istore_invariant (from - 1) e e' l

let sl_pure_imp_elim (p:prop) (q: squash p -> slprop)
  : Lemma (p ==> sl_pure_imp p q == q ())
  = introduce p ==> sl_pure_imp p q == q ()
    with _ . (
      slprop_extensionality (sl_pure_imp p q) (q ())
    )

let rec move_invariant (e:inames) (l:istore) (p:slprop) (from:nat)
                       (i:iname{iname_for_p i p l /\ from >= i /\ ~(i `Set.mem` e)})
: Lemma (ensures 
               (istore_invariant from e l) ==
               (p `star` istore_invariant from (set_add i e) l))
        (decreases from)
= calc (==) {
    istore_invariant from e l;
    (==) {}
    invariant_of_one_cell from e l `star` (if from = 0 then emp else (istore_invariant (from - 1) e l));
  };
  if i = from
  then (
    let Some c = H0.select i l in
    assert (cell_pred_pre c);
    sl_pure_imp_elim (cell_pred_pre c) (cell_pred_post c);
    assert (invariant_of_one_cell from e l == p);
    if from = 0
    then (
      assert (istore_invariant 0 (set_add i e) l == emp `star` emp);
      emp_unit emp;
      slprop_extensionality (emp `star` emp) emp;
      assert (emp `star` emp == emp)
    )
    else (
      calc (==) {
        istore_invariant from (set_add i e) l;
      (==) {}
        invariant_of_one_cell from (set_add i e) l `star` (istore_invariant (from - 1) (set_add i e) l);
      (==) {}
        emp `star` (istore_invariant (from - 1) (set_add i e) l);
      (==) { star_comm emp (istore_invariant (from - 1) (set_add i e) l) }
        istore_invariant (from - 1) (set_add i e) l `star` emp;
      (==) { emp_u (istore_invariant (from - 1) (set_add i e) l)}
        istore_invariant (from - 1) (set_add i e) l;
      (==) { weaken_inames_istore_invariant (from - 1) e (Set.singleton i) l }
        istore_invariant (from - 1) e l;
      }
    )
  )
  else (
    move_invariant e l p (from - 1) i;
    calc (==) {
      istore_invariant from e l;
    (==) {}
      invariant_of_one_cell from e l `star` (p `star` istore_invariant (from - 1) (set_add i e) l);
    (==) { _ by (T.mapply (`pqr_qpr))}
      p `star` (invariant_of_one_cell from e l `star` istore_invariant (from - 1) (set_add i e) l);
    (==) { }
      p `star` (invariant_of_one_cell from (set_add i e) l `star` istore_invariant (from - 1) (set_add i e) l);
    }
  )

(** Any separation logic proposition valid over [m] is also valid on [core_mem m] *)
let core_mem_interp (hp:slprop u#a) (m:mem u#a)
  : Lemma
      (requires True)
      (ensures (interp hp (core_mem m) <==> interp hp m))
      [SMTPat (interp hp (core_mem m))]
  = ()

let refined_pre_action mg e (fp0:slprop) (a:Type) (fp1:a -> slprop) =
  m0:hmem_with_inv_except e fp0 ->
  Pure (x:a &
        hmem_with_inv_except e (fp1 x))
       (requires True)
       (ensures fun  (| x, m1 |) ->
         maybe_ghost_action mg m0 m1 /\
         frame_related_mems fp0 (fp1 x) e m0 m1)

let tot_pre_action_nf_except (maybe_ghost:bool) (e:inames) (fp:slprop u#a) (a:Type u#b) (fp':a -> slprop u#a) =
  m0:hmem_with_inv_except e fp ->
  res:(x:a & hmem_with_inv_except e (fp' x)) { maybe_ghost_action maybe_ghost m0 (dsnd res)}

let tot_pre_action_nf maybe_ghost = tot_pre_action_nf_except maybe_ghost S.empty

let ac_reasoning_for_m_frame_preserving
    (p q r:slprop u#a) (m:mem u#a)
  : Lemma
    (requires interp ((p `star` q) `star` r) m)
    (ensures interp (p `star` r) m)
  = calc (equiv) {
    (p `star` q) `star` r;
       (equiv) { star_commutative p q;
                 slprop_extensionality (p `star` q) (q `star` p) }
    (q `star` p) `star` r;
       (equiv) { star_associative q p r }
    q `star` (p `star` r);
    };
    assert (interp (q `star` (p `star` r)) m);
    affine_star q (p `star` r) m

let is_frame_preserving
  (#mg:bool)
  (#e:inames)
  (#a:Type u#b)
  (#fp:slprop u#a)
  (#fp':a -> slprop u#a)
  (f:tot_pre_action_nf_except mg e fp a fp') =
  forall (frame:slprop u#a) (m0:hmem_with_inv_except e (fp `star` frame)).
    (ac_reasoning_for_m_frame_preserving fp frame (mem_invariant e m0) m0;
     let (| x, m1 |) = f m0 in
     interp ((fp' x `star` frame) `star` mem_invariant e m1) m1 /\
     mem_evolves m0 m1)

let tot_action_nf_except (mg:bool) (e:inames) (fp:slprop u#a) (a:Type u#b) (fp':a -> slprop u#a) =
  f:tot_pre_action_nf_except mg e fp a fp'{ is_frame_preserving f }

let refined_pre_action_as_action (#fp0:slprop) (#a:Type) (#fp1:a -> slprop)
                                 #mg #e ($f:refined_pre_action mg e fp0 a fp1)
  : tot_action_nf_except mg e fp0 a fp1
  = let g : tot_pre_action_nf_except mg e fp0 a fp1 = fun m -> f m in
    introduce 
      forall (frame:slprop)
             (m0:hmem_with_inv_except e (fp0 `star` frame)).
              (ac_reasoning_for_m_frame_preserving fp0 frame (mem_invariant e m0) m0;
                let (| x, m1 |) = g m0 in
                interp ((fp1 x `star` frame) `star` mem_invariant e m1) m1 /\
                mem_evolves m0 m1)
      with (
        ac_reasoning_for_m_frame_preserving fp0 frame (mem_invariant e m0) m0;
        let (| x', m1' |) = g m0 in
        let (| x, m1 |) = f m0 in
        assert (x == x' /\ m1 == m1')
    );
    g

let pqr_prq (p q r:slprop)
  : Lemma (((p `star` q) `star` r) == (p `star` r) `star` q)
  = calc (==) {
      (p `star` q) `star` r;
    (==) { star_assoc p q r }
      p `star` (q `star` r);
    (==) { star_comm q r }
      p `star` (r `star` q);
    (==) { star_assoc p r q }
      (p `star` r) `star` q;
    }

let frame_preserving_respects_preorder #mg #a #e #fp #fp' ($f:tot_action_nf_except mg e fp a fp') (m0:hmem_with_inv_except e fp)
  : Lemma (let (| x, m1 |) = f m0 in
           mem_evolves m0 m1)
  = assert (is_frame_preserving f);
    emp_u fp
    
let lift_tot_action #a #mg #e #fp #fp'
  ($f:tot_action_nf_except mg e fp a fp')
: _pst_action_except a mg e fp fp'
= fun (frame:slprop) m0 ->
    ac_reasoning_for_m_frame_preserving fp frame (mem_invariant e m0) m0;
    assert (interp (fp `star` frame `star` mem_invariant e m0) m0);
    assert (interp (fp `star` mem_invariant e m0) m0);
    let m0' : hmem_with_inv_except e fp = m0 in
    let r = f m0' in
    let (| x, m1 |) = r in
    let m1' : hmem_with_inv_except e (fp' x) = m1 in
    assert (is_frame_preserving f);
    assert (m1 == dsnd (f m0));
    frame_preserving_respects_preorder f m0;
    (x, m1)
#restart-solver
#push-options "--fuel 0 --ifuel 0"
let intro_pure_star (p:slprop) (q:prop) (m:mem)
  : Lemma (interp p m /\ q ==> interp (p `star` pure q) m)
  = introduce
      interp p m /\ q ==> interp (p `star` pure q) m
    with _ . (
      let m0 = {m with iheap=empty_iheap} in
      assert (interp (pure q) {m with iheap=empty_iheap});
      assert (disjoint m m0)
    )

let intro_star (p q:slprop) (m0 m1:mem)
: Lemma
  (requires
     disjoint m0 m1 /\
     interp p m0 /\
     interp q m1)
  (ensures
     interp (p `star` q) (join m0 m1))
= ()
#restart-solver

let h0_emp_unit (p:H0.slprop)
  : Lemma (H0.( emp `star` p == p `star` emp /\ p `star` emp == p))
  = let open H0 in
    H0.star_commutative p H0.emp;
    H0.slprop_extensionality (p `star` emp) (emp `star` p);
    H0.emp_unit p;
    H0.slprop_extensionality (p `H0.star` H0.emp) p

let h0_of_as_slprop (p:H0.a_heap_prop) (h:H0.heap)
  : Lemma (h0_of_slprop (H0.as_slprop p) h <==> p h)
  = ()

let mem_evolves_iff (h0 h1:full_mem)
: Lemma 
  (ensures
     mem_evolves h0 h1 <==> (
      H2.heap_evolves h0.iheap.concrete h1.iheap.concrete /\
      h0.iname_ctr <= h1.iname_ctr /\
      istore_evolves h0.iheap.invariants h1.iheap.invariants))
= assert (mem_evolves h0 h1 <==> 
            (H2.heap_evolves h0.iheap.concrete h1.iheap.concrete /\
             h0.iname_ctr <= h1.iname_ctr /\
             istore_evolves h0.iheap.invariants h1.iheap.invariants))
      by (FStar.Tactics.norm [delta_only [`%mem_evolves]])


#push-options "--fuel 1"
let sl_pure_imp_big (p:prop) (q: squash p -> slprop)
: Lemma
  (requires p ==> is_big (q ()))
  (ensures is_big (sl_pure_imp p q))
= eliminate p \/ ~p
  returns is_big (sl_pure_imp p q)
  with _ . (
    assert (forall h. sl_pure_imp p q h <==> q () h);
    slprop_extensionality (sl_pure_imp p q) (q ())
  )
  and _ . (
    introduce forall h. emp h
    with ( H2.intro_emp h.concrete ); 
    assert (forall h. sl_pure_imp p q h <==> emp h);
    slprop_extensionality (sl_pure_imp p q) emp
  )

let invariant_of_one_cell_is_big (from:nat) (e:inames) (i:istore)
: Lemma (is_big (invariant_of_one_cell from e i))
= if from `S.mem` e then ()
  else match H0.select from i with
       | None -> ()
       | Some c ->
         introduce cell_pred_pre c ==> is_big (cell_pred_post c ())
         with _ . (
            let H0.Ref _ _ _ v = c in
            let v : PA.agreement H2.slprop = v in
            match v with
            | None -> ()
            | Some p -> ()
         );
         sl_pure_imp_big (cell_pred_pre c) (cell_pred_post c)

let rec istore_invariant_is_big (from:nat) (e:inames) (i:istore)
: Lemma (is_big (istore_invariant from e i))
= invariant_of_one_cell_is_big from e i;
  if from = 0
  then (
    emp_u (invariant_of_one_cell from e i)
  )
  else (
    istore_invariant_is_big (from - 1) e i;
    big_star_congruence (invariant_of_one_cell from e i) (istore_invariant (from - 1) e i)
  )
#pop-options

let mem_invariant_is_big (e:inames) (m:mem)
: Lemma (is_big (mem_invariant e m))
= istore_invariant_is_big m.iname_ctr e m.iheap.invariants;
  big_star_congruence
    (istore_invariant m.iname_ctr e m.iheap.invariants)
    (ctr_validity m.ctr m.ghost_ctr m.iname_ctr m.iheap)
  
let big_slprop_depends_only_on_concrete
    (p:slprop { is_big p })
    (m0 m1:mem)
  : Lemma 
    (requires interp p m0 /\ m0.iheap.concrete == m1.iheap.concrete)
    (ensures interp p m1)
  = ()

let big_inv_star (p:H0.slprop) (q:slprop { is_big q })  (m:mem)
: Lemma 
  (requires interp (lift_h0 p) m /\ interp q m)
  (ensures interp (lift_h0 p `star` q) m)
= let ml = { m with iheap={m.iheap with concrete = H2.empty_heap }} in
  let mr = { m with iheap={m.iheap with invariants = H0.empty_heap }} in
  assert (interp (lift_h0 p) ml);
  assert (interp q mr);
  assert (disjoint ml mr)

#push-options "--fuel 1"
let cell_of (i:iname) (l:istore { Some? (H0.select i l) })
: GTot H0.cell
= Some?.v (H0.select i l)

let istore_invariant_after_extend
      (e:inames)
      (iname:nat)
      (p : slprop { is_big p })
      (m0 : full_mem)
      (invs0:H0.full_hheap H0.emp { 
        H0.free_above_addr invs0 iname /\
        reveal m0.iheap.invariants == invs0 /\
        iname == reveal m0.iname_ctr /\
        inames_ok e m0 /\
        heap_ctr_valid m0.ctr m0.ghost_ctr m0.iname_ctr m0.iheap})
: Lemma (
    let (| v, inv1 |) = H0.extend #_ #(PA.pcm_agreement #H2.slprop) (Some (down p)) iname invs0 in
    let m1 = { m0 with iname_ctr=iname + 1; iheap = {m0.iheap with invariants = inv1} } in
    istore_invariant m1.iname_ctr e m1.iheap.invariants ==
    p `star` istore_invariant m0.iname_ctr e m0.iheap.invariants /\
    inames_ok e m1 /\
    istore_evolves m0.iheap.invariants m1.iheap.invariants /\
    heap_ctr_valid m1.ctr m1.ghost_ctr m1.iname_ctr m1.iheap /\
    (p `star` mem_invariant e m0 == mem_invariant e m1)
  )
= let (| v, inv1 |) = H0.extend #_ #(PA.pcm_agreement #H2.slprop) (Some (down p)) iname invs0 in
  let m1 = { m0 with iname_ctr=iname + 1; iheap = {m0.iheap with invariants = inv1} } in
  H0.extend_modifies_nothing #_ #(PA.pcm_agreement #H2.slprop) (Some (down p)) iname invs0;
  assert (m1.iheap.concrete `H2.free_above_addr CONCRETE` m1.ctr);
  H0.interp_free_above invs0 iname;
  calc (==) {
    istore_invariant m1.iname_ctr e m1.iheap.invariants;
    (==) {}
    invariant_of_one_cell (iname + 1) e inv1
    `star` istore_invariant iname e inv1;
    (==) { assert (H0.select (iname + 1) inv1 == None) }
    emp `star` istore_invariant iname e inv1;
    (==) { emp_u (istore_invariant iname e inv1) }
    istore_invariant iname e inv1;
    (==)  {}
    invariant_of_one_cell iname e inv1 `star` (if iname = 0 then emp else istore_invariant (iname - 1) e inv1);
    (==) { assert (Some? (H0.select iname inv1)); assert (not (iname `Set.mem` e))  }
    sl_pure_imp (cell_pred_pre (cell_of iname inv1)) (cell_pred_post (cell_of iname inv1))
    `star`
    (if iname = 0 then emp else istore_invariant (iname - 1) e inv1);
    (==) { sl_pure_imp_elim (cell_pred_pre (cell_of iname inv1)) (cell_pred_post (cell_of iname inv1)) }
    p `star`
    (if iname = 0 then emp else istore_invariant (iname - 1) e inv1);
    };
    assert (H0.select iname invs0 == None);
    calc (==) {
      istore_invariant iname e invs0; 
    (==) { }
      emp `star` (if iname = 0 then emp else istore_invariant (iname - 1) e invs0);
    (==) { emp_u (if iname = 0 then emp else istore_invariant (iname - 1) e invs0) }
      (if iname = 0 then emp else istore_invariant (iname - 1) e invs0);
    };
    assert (forall i. i < iname ==> H0.select i invs0 == H0.select i inv1);
    let rec aux (i:nat { i < iname })
        : Lemma  (istore_invariant i e invs0 == istore_invariant i e inv1)
        = if i = 0
          then ()
          else (
            aux (i - 1)
          )
    in
    if iname = 0
    then ()
    else (
      aux (iname - 1);
      assert (istore_invariant (iname - 1) e invs0 ==
              istore_invariant (iname - 1) e inv1)
    );
    calc (==) {
      p `star` mem_invariant e m0;
    (==) {}
      p `star` 
      (istore_invariant m0.iname_ctr e m0.iheap.invariants `star`
      ctr_validity m0.ctr m0.ghost_ctr m0.iname_ctr m0.iheap);
    (==) { _ by (T.mapply (`star_assoc)) }
    (p `star` 
      istore_invariant m0.iname_ctr e m0.iheap.invariants) `star`
      ctr_validity m0.ctr m0.ghost_ctr m0.iname_ctr m0.iheap;
    (==) { }
      istore_invariant m1.iname_ctr e m1.iheap.invariants `star`
      ctr_validity m0.ctr m0.ghost_ctr m0.iname_ctr m0.iheap;
    };
    calc (==) {
      ctr_validity m0.ctr m0.ghost_ctr m0.iname_ctr m0.iheap;
      (==) {}
      pure (heap_ctr_valid m0.ctr m0.ghost_ctr m0.iname_ctr m0.iheap);
      (==) { 
        FStar.PropositionalExtensionality.apply
          (heap_ctr_valid m0.ctr m0.ghost_ctr m0.iname_ctr m0.iheap)
          (heap_ctr_valid m1.ctr m1.ghost_ctr m1.iname_ctr m1.iheap)

       }
      ctr_validity m1.ctr m1.ghost_ctr m1.iname_ctr m1.iheap;      
    }

#pop-options
#push-options "--split_queries no --z3rlimit_factor 2"           
let new_invariant_pre_action (e:inames) (p:slprop u#a { is_big p })
: refined_pre_action true e p iname_ref (fun i -> iname_ref_pts_to i p)
= fun (m0:hmem_with_inv_except e p) ->
    let iname = m0.iname_ctr in
    assert (interp (p `star` mem_invariant e m0) m0);
    assert (interp (p `star` istore_invariant m0.iname_ctr e m0.iheap.invariants) m0);
    assert (interp (pure (heap_ctr_valid m0.ctr m0.ghost_ctr iname (heap_of_mem m0))) m0);
    assert (H0.free_above_addr m0.iheap.invariants iname);
    assert (full_mem_pred m0);
    assert (H0.full_heap_pred m0.iheap.invariants);
    let res 
      : erased (x:H0.ref _ _ & H0.full_hheap (H0.pts_to #_ #(PA.pcm_agreement #(H2.slprop u#a)) x (Some (down p))))
      = H0.intro_emp m0.iheap.invariants;
        Ghost.hide <| H0.extend #_ #(PA.pcm_agreement) (Some (down p)) iname m0.iheap.invariants
    in
    let x : iname_ref = dfst res in
    let inv1 : istore (* erased (H0.full_hheap (H0.pts_to x (Some (down p)))) *) = dsnd res in
    let iheap1 = { m0.iheap with invariants = inv1 } in
    let m1 = { m0 with iname_ctr = iname + 1; iheap = iheap1 } in
    assert (full_mem_pred m1);
    assert (heap_ctr_valid m1.ctr m1.ghost_ctr m1.iname_ctr m1.iheap);
    istore_invariant_after_extend e iname p m0 m0.iheap.invariants;  
    assert (istore_invariant m1.iname_ctr e m1.iheap.invariants ==
            p `star` istore_invariant m0.iname_ctr e m0.iheap.invariants);
    assert (interp (istore_invariant m1.iname_ctr e m1.iheap.invariants) m0);
    istore_invariant_is_big m1.iname_ctr e m1.iheap.invariants;
    big_slprop_depends_only_on_concrete p m0 m1;
    (* istore_invariants is a lifting of a conjunction of ups; so, since m0.iheap.concrete didn't change, this should hold *)
    assert (interp (istore_invariant m1.iname_ctr e m1.iheap.invariants) m1);
    intro_pure_star
      (istore_invariant m1.iname_ctr e m1.iheap.invariants)
      (heap_ctr_valid m1.ctr m1.ghost_ctr m1.iname_ctr m1.iheap)
      m1;
    assert (interp (mem_invariant e m1) m1);
    assert (H0.interp (H0.pts_to #_ #(PA.pcm_agreement #(H2.slprop u#a)) x (Some (down p))) m1.iheap.invariants);
    assert (interp (iname_ref_pts_to x p) m1);
    mem_invariant_is_big e m1;
    big_inv_star (H0.pts_to #_ #(PA.pcm_agreement #(H2.slprop u#a)) x (Some (down p))) (mem_invariant e m1) m1;
    assert (interp (iname_ref_pts_to x p `star` mem_invariant e m1) m1);
    assert (inames_ok e m1);
    let res : (x:iname_ref & hmem_with_inv_except e (iname_ref_pts_to x p)) = (| x, m1 |) in
    assert (maybe_ghost_action true m0 m1);
    let aux (frame:slprop)
      : Lemma 
        (requires interp ((p `star` frame) `star` mem_invariant e m0) m0)
        (ensures interp ((iname_ref_pts_to x p `star` frame) `star` mem_invariant e m1) m1 /\
                 mem_evolves m0 m1)
        [SMTPat (p `star` frame)]
      = let pick_frame =
          fun (i:H0.heap) ->
            interp ((p `star` frame) `star` mem_invariant e m0)
                   {m0 with iheap={m0.iheap with invariants=i}} in
        (* proof of affinity *)
        let _ = 
          introduce forall h0 h1.
              pick_frame h0 /\ H0.disjoint h0 h1
              ==> pick_frame (H0.join h0 h1)
          with (
            introduce _ ==> _
            with _ . (
                let left = { m0.iheap with invariants = h0 } in
                let right = { concrete=H2.empty_heap; invariants = h1} in
                assert (idisjoint left right)
            )
          )
        in
        assert (H0.heap_prop_is_affine pick_frame);
        assert (pick_frame m0.iheap.invariants);
        let frm : H0.slprop = H0.as_slprop pick_frame in
        assert(H0.interp frm m0.iheap.invariants);
        h0_emp_unit frm;
        assert (H0.interp (H0.emp `H0.star` frm) m0.iheap.invariants);
        let inv0 : H0.full_hheap (H0.emp `H0.star` frm) = m0.iheap.invariants in
        H0.action_framing 
          (H0.extend #_ #(PA.pcm_agreement) (Some (down p)) iname)
          frm
          inv0;
        assert (H0.interp (H0.pts_to #_ #(PA.pcm_agreement #(H2.slprop u#a)) x (Some (down p)) `H0.star` frm)
                          inv1);
        assert (interp 
          (lift_h0 
            (H0.pts_to #_ #(PA.pcm_agreement #(H2.slprop u#a)) x (Some (down p)) `H0.star` frm))
          m1);
        star_congruence_h0 (H0.pts_to #_ #(PA.pcm_agreement #(H2.slprop u#a)) x (Some (down p))) frm;
        assert (interp (iname_ref_pts_to x p `star` lift_h0 frm) m1);
        eliminate 
          exists h1_0 h1_1.
              idisjoint h1_0 h1_1 /\
              m1.iheap == ijoin h1_0 h1_1 /\
              (iname_ref_pts_to x p) h1_0 /\
              (lift_h0 frm) h1_1
          returns
              interp 
                ((iname_ref_pts_to x p `star` frame) `star`
                  mem_invariant e m1)
                m1
          with _ . (
            assert 
              (h0_of_slprop (H0.as_slprop pick_frame) h1_1.invariants);
            h0_of_as_slprop pick_frame h1_1.invariants;
            assert (pick_frame h1_1.invariants);
            let m1_0 = { m1 with iheap = { concrete = H2.empty_heap; invariants = h1_0.invariants } } in
            assert (interp (iname_ref_pts_to x p) m1_0);
            let m1_1 = { m1 with iheap = {m1.iheap with invariants=h1_1.invariants}} in
            assert (interp ((p `star` frame) `star` mem_invariant e m0) m1_1);
            star_assoc p frame (mem_invariant e m0);
            pqr_qpr p frame (mem_invariant e m0);
            assert ((p `star` frame) `star` mem_invariant e m0 ==
                    frame `star` (p `star` mem_invariant e m0));
            assert (p `star` mem_invariant e m0 == mem_invariant e m1); 
            assert (interp (frame `star` mem_invariant e m1) m1_1);
            assert (disjoint m1_0 m1_1);
            assert (m1 == join m1_0 m1_1);
            intro_star (iname_ref_pts_to x p) (frame `star` mem_invariant e m1) m1_0 m1_1;
            assert (interp (iname_ref_pts_to x p `star` (frame `star` mem_invariant e m1)) m1);
            star_assoc (iname_ref_pts_to x p) frame (mem_invariant e m1)
          );
        assert (H2.heap_evolves m0.iheap.concrete m1.iheap.concrete);
        assert (istore_evolves m0.iheap.invariants m1.iheap.invariants);
        mem_evolves_iff m0 m1
    in
    assert (frame_related_mems p (iname_ref_pts_to x p) e m0 m1);
    res
#pop-options
#pop-options

let name_of_inv (i:iname_ref) = H0.core_ref_as_addr i
let ( -~- ) (i:iname_ref) (p:slprop u#a) = iname_ref_pts_to i p

let lift_h0_star (p q:H0.slprop)
: Lemma (lift_h0 (p `H0.star` q) == lift_h0 p `star` lift_h0 q)
= star_congruence_h0 p q

let dup_inv_lemma (i:iname_ref) (p:slprop) frame (m:mem)
: Lemma (requires interp ((i -~- p) `star` frame) m)
        (ensures interp (((i -~- p) `star` (i -~- p)) `star` frame) m)
= let h = m.iheap in
  eliminate exists h0 h1.
    idisjoint h0 h1 /\
    m.iheap == ijoin h0 h1 /\
    (i -~- p) h0 /\
    frame h1
  returns interp (((i -~- p) `star` (i -~- p)) `star` frame) m
  with _ . (
    let pcm = PA.pcm_agreement #(H2.slprop u#a) in
    assert (H0.interp (H0.pts_to #_ #pcm i (Some (down p))) h0.invariants);
    assert (H0.interp (H0.pts_to #_ #pcm i (op pcm (Some (down p)) (Some (down p)))) h0.invariants);
    H0.pts_to_compatible #_ #(PA.pcm_agreement #(H2.slprop u#a)) i (Some (down p)) (Some (down p)) h0.invariants;
    assert (H0.interp (H0.pts_to #_ #pcm i (Some (down p)) `H0.star`
                       H0.pts_to #_ #pcm i (Some (down p))) h0.invariants);
    assert ( (lift_h0 
                      (H0.pts_to #_ #pcm i (Some (down p)) `H0.star`
                                        H0.pts_to #_ #pcm i (Some (down p))))
                    h0);
    lift_h0_star (H0.pts_to #_ #pcm i (Some (down p)))
                 (H0.pts_to #_ #pcm i (Some (down p)));
    assert (((i -~- p) `star` (i -~- p)) h0)
  )

let dup_inv e i p =
  fun (frame:slprop) (m:hmem_with_inv_except e ((i -~- p) `star` frame)) ->
    assert (interp (((i -~- p) `star` frame) `star` mem_invariant e m) m);
    FStar.Classical.forall_intro_3 star_assoc;
    dup_inv_lemma i p (frame `star` mem_invariant e m) m;
    assert (interp (((i -~- p) `star` (i -~- p)) `star` (frame `star` mem_invariant e m)) m);
    let m : hmem_with_inv_except e (((i -~- p) `star` (i -~- p)) `star` frame) = m in
    ((), m)


let new_invariant (e:inames) (p:slprop u#a { is_big p })
: pst_ghost_action_except iname_ref e p (fun i -> i -~- p)
= lift_tot_action (refined_pre_action_as_action (new_invariant_pre_action e p))


#push-options "--fuel 0 --ifuel 0 --split_queries no --z3rlimit_factor 2"
let move_mem_invariant
        (e:inames)
        (m:mem)
        (p:slprop)
        (i:iname{
            iname_for_p i p m.iheap.invariants /\
            m.iname_ctr >= i /\
            ~(i `Set.mem` e)
        })
: Lemma 
  (ensures 
    mem_invariant e m ==
    (p `star` mem_invariant (set_add i e) m))
= move_invariant e m.iheap.invariants p m.iname_ctr i;
  star_assoc p 
            (istore_invariant m.iname_ctr (set_add i e) m.iheap.invariants) 
            (ctr_validity m.ctr m.ghost_ctr m.iname_ctr m.iheap)
  
let elim_inv e (i:iname_ref) (p:slprop { is_big p }) (m:mem)
: Lemma
  (requires interp (i -~- p) m /\ interp (mem_invariant e m) m)
  (ensures iname_for_p (name_of_inv i) p m.iheap.invariants /\
           m.iname_ctr >= name_of_inv i /\
           not (H0.core_ref_is_null i))
= assert (interp (pure (heap_ctr_valid m.ctr m.ghost_ctr m.iname_ctr m.iheap)) m);
  assert (H0.interp (H0.pts_to #_ #(PA.pcm_agreement #(H2.slprop u#a)) i (Some (down p))) m.iheap.invariants);
  H0.interp_pts_to i #_ #(PA.pcm_agreement #(H2.slprop u#a)) (Some (down p)) m.iheap.invariants;
  H0.interp_free_above m.iheap.invariants m.iname_ctr
  
let pqrst_sq_pr_t (p q r s t : slprop)
: Lemma (p `star` q `star` r `star` (s `star` t) == (s `star` q) `star` (p `star` r) `star` t)
= FStar.Classical.forall_intro_3 star_assoc;
  FStar.Classical.forall_intro_2 star_comm

let elim_star_pq (p q:slprop) (m:mem)
: Lemma 
  (requires interp (p `star` q) m)
  (ensures interp p m /\ interp q m)
= ()

let elim_star_pqrs (p q r s:slprop) (m:mem)
: Lemma 
  (requires interp (p `star` q `star` r `star` s) m)
  (ensures 
    interp p m /\
    interp q m /\
    interp r m /\
    interp s m)
= ()

let with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#e:inames)
                   (#p:slprop { is_big p })
                   (#maybe_ghost:bool)
                   (i:iname_ref{not (mem_inv e i)})
                   (f:_pst_action_except a maybe_ghost
                        (add_inv e i) 
                        (p `star` fp)
                        (fun x -> p `star` fp' x))
: _pst_action_except a maybe_ghost e
      ((i -~- p) `star` fp)
      (fun x -> (i -~- p) `star` fp' x)
= fun (frame:slprop) (m0:hmem_with_inv_except e(((i -~- p) `star` fp) `star` frame)) ->
    assert (interp ((i -~- p) `star` fp `star` frame `star` mem_invariant e m0) m0);
    assert (interp ((i -~- p)) m0);
    elim_star_pqrs (i -~- p) fp frame (mem_invariant e m0) m0;
    assert (interp (mem_invariant e m0) m0);
    elim_inv e i p m0;
    move_mem_invariant e m0 p (name_of_inv i);
    assert (interp ((i -~- p) `star` fp `star` frame `star` (p `star` mem_invariant (set_add (name_of_inv i) e) m0)) m0);
    assert (Set.equal (set_add (name_of_inv i) e) (add_inv e i));
    assert (
        ((i -~- p) `star` fp `star` frame `star` (p `star` mem_invariant (add_inv e i) m0)) ==
        (((p `star` fp) `star` ((i -~- p) `star` frame) `star` mem_invariant (add_inv e i) m0))
      ) by (T.mapply (`pqrst_sq_pr_t));
    assert (inames_ok (set_add (name_of_inv i) e) m0);
    let m0 : hmem_with_inv_except (add_inv e i) ((p `star` fp) `star` ((i -~- p) `star` frame)) = m0 in
    let (x, m1) = f ((i -~- p) `star` frame) m0 in
    let m1 : hmem_with_inv_except (add_inv e i) ((p `star` fp' x) `star` ((i -~- p) `star` frame)) = m1 in
    assert (interp (((p `star` fp' x) `star` ((i -~- p) `star` frame)) `star` mem_invariant (add_inv e i) m1) m1);
    assert (
        (((i -~- p) `star` fp' x) `star` frame `star` (p `star` mem_invariant (add_inv e i) m1)) ==
        (((p `star` fp' x) `star` ((i -~- p) `star` frame)) `star` mem_invariant (add_inv e i) m1)
      ) by (T.mapply (`pqrst_sq_pr_t));
    assert (interp (((i -~- p) `star` fp' x) `star` frame) m1);
    assert (interp (i -~- p) m1);
    elim_star_pq 
       ((p `star` fp' x) `star` ((i -~- p) `star` frame)) 
       (mem_invariant (add_inv e i) m1)
       m1;
    assert (interp (mem_invariant (add_inv e i) m1) m1);
    elim_inv (add_inv e i) i p m1;
    mem_evolves_iff m0 m1;
    move_mem_invariant e m1 p (name_of_inv i);             
    let m1 : hmem_with_inv_except e (((i -~- p) `star` fp' x) `star` frame) = m1 in
    (x, m1)
#pop-options

let distinct_invariants_have_distinct_names
      (e:inames)
      (p:big_vprop u#m)
      (q:big_vprop u#m { p =!= q })
      (i j: iname_ref)
: pst_ghost_action_except u#0 u#m 
    (squash (name_of_inv i =!= name_of_inv j))
    e 
    ((i -~- p) `star` (j -~- q))
    (fun _ -> (i -~- p) `star` (j -~- q))
= fun frame m0 ->
    elim_star_pqrs (i -~- p) (j -~- q) frame (mem_invariant e m0) m0;
    elim_inv e i p m0;
    elim_inv e j q m0;
    ((), m0)

let invariant_name_identifies_invariant
      (e:inames)
      (p q:big_vprop u#m)
      (i:iname_ref)
      (j:iname_ref { name_of_inv i == name_of_inv j } )
: pst_ghost_action_except (squash (p == q /\ i == j)) e
   ((i -~- p) `star` (j -~- q))
   (fun _ -> (i -~- p) `star` (j -~- q))
= fun frame m0 ->
    elim_star_pqrs (i -~- p) (j -~- q) frame (mem_invariant e m0) m0;
    elim_inv e i p m0;
    elim_inv e j q m0;
    let open H0 in
    addr_core_ref_injective_2 i;
    addr_core_ref_injective_2 j;    
    ((), m0)

let fresh_invariant (e:inames) (p:slprop u#m) (ctx:list iname_ref)
: pst_ghost_action_except (i:iname_ref { fresh_wrt ctx i }) e
       (p `star` all_live ctx)
       (fun i -> i -~- p)
= admit()

let equiv_pqrs_p_qr_s (p q r s:slprop)
  : Lemma ((p `star` q `star` r `star` s) ==
           (p `star` (q `star` r) `star` s))
  = star_associative p q r;
    slprop_extensionality
      (p `star` q `star` r)
      (p `star` (q `star` r))

let pst_frame
          (#a:Type)
          (#mg:_)
          (#opened_invariants:inames)
          (#pre:slprop)
          (#post:a -> slprop)
          (frame:slprop)
          ($f:_pst_action_except a mg opened_invariants pre post)
: _pst_action_except a mg opened_invariants (pre `star` frame) (fun x -> post x `star` frame)
= fun frame0 m0 ->
    equiv_pqrs_p_qr_s pre frame frame0 (mem_invariant opened_invariants m0);
    assert (interp (pre `star` frame `star` frame0 `star` mem_invariant opened_invariants m0) m0);
    assert (interp (pre `star` (frame `star` frame0) `star` mem_invariant opened_invariants m0) m0);
    let x, m1 = f (frame `star` frame0) m0 in
    equiv_pqrs_p_qr_s (post x) frame frame0 (mem_invariant opened_invariants m1);
    assert (interp (post x `star` (frame `star` frame0) `star` mem_invariant opened_invariants m1) m1);
    assert (interp (post x `star` frame `star` frame0 `star` mem_invariant opened_invariants m1) m1);
    x, m1

let mg_of_mut (m:mutability) =
  match m with
  | MUTABLE -> false
  | _ -> true

#restart-solver
// let elim_frame_related_mems
//      (fp fp':_)
//      (e:inames)
//      (m0:hmem_with_inv m1:mem)
// : Lemma
//   (requires 
//     frame_related_mems fp fp' e m0 m1 /\
//     interp (fp `star` mem_invariant e m0) m0)
//   (ensures
//     interp (fp' `star` mem_invariant e m1) m1 /\
//     mem_evolves m0 m1)
// = ()

let elim_mem_invariant e m
: Lemma
  (requires interp (mem_invariant e m) m)
  (ensures 
    interp (istore_invariant m.iname_ctr e m.iheap.invariants) m /\
    heap_ctr_valid m.ctr m.ghost_ctr m.iname_ctr m.iheap)
= elim_star_pq 
    (istore_invariant m.iname_ctr e m.iheap.invariants)
    (ctr_validity m.ctr m.ghost_ctr m.iname_ctr m.iheap)
    m

let mem_invariant_eq e m0 m1
: Lemma 
  (requires
    m0.iheap.invariants == m1.iheap.invariants /\
    m0.iname_ctr == m1.iname_ctr /\
    heap_ctr_valid m0.ctr m0.ghost_ctr m0.iname_ctr m0.iheap /\
    heap_ctr_valid m1.ctr m1.ghost_ctr m1.iname_ctr m1.iheap)
  (ensures mem_invariant e m0 == mem_invariant e m1)
= FStar.PropositionalExtensionality.apply 
    (heap_ctr_valid m0.ctr m0.ghost_ctr m0.iname_ctr m0.iheap)
    (heap_ctr_valid m1.ctr m1.ghost_ctr m1.iname_ctr m1.iheap)

let elim_h2_frame_preserving
  (#a: Type)
  (#pre #post:_)
  (#fp: H2.slprop)
  (#fp': a -> H2.slprop)
  (#immut:mutability)
  (#allocates:option tag)
  ($f:H2.action #immut #allocates #pre #post fp a fp')
  (h0:H2.full_hheap fp { pre h0 })
: Lemma
  (ensures (
    let (| x, h1 |) = f h0 in
    H2.action_related_heaps #immut #allocates h0 h1))
= let open H2 in
  assert (is_frame_preserving immut allocates f);
  H2.emp_unit fp;
  assert (H2.interp (fp `star` emp) h0);
  affine_star fp emp h0;
  eliminate
    forall (frame: slprop) (h0:full_hheap (fp `star` frame) { pre h0 }).
     (affine_star fp frame h0;
      let (| x, h1 |) = f h0 in
      interp (fp' x `star` frame) h1 /\
      action_related_heaps #immut #allocates h0 h1)
  with emp h0

#restart-solver
#push-options "--fuel 0 --ifuel 1 --split_queries no --z3rlimit_factor 2"

let h2_action_framing
  (#a: Type)
  (#mut #allocates:_)
  (#pre #post:_)
  (#fp: H2.slprop)
  (#fp': a -> H2.slprop)
  ($f:H2.action #mut #allocates #pre #post fp a fp')
  (frame:H2.slprop) (h0:H2.full_hheap (fp `H2.star` frame) { pre h0 })
: Lemma (
      H2.affine_star fp frame h0;
      let (| x, h1 |) = f h0 in
      H2.frame_related_heaps h0 h1 fp (fp' x) frame mut allocates
    )
= admit()

let frame_heap_action
  (#a: Type)
  (#pre #post:_)
  (#fp: H2.slprop)
  (#fp': a -> H2.slprop)
  (#immut:mutability)
  (#allocates:option tag)
  ($f:H2.action #immut #allocates #pre #post fp a fp')
  (e:inames)
  (m0:hmem_with_inv_except e (up fp) { pre m0.iheap.concrete })
  (m1:mem {
    let (| x, h1 |) = f m0.iheap.concrete in
    m1.iheap.concrete == h1 /\
    m1.iheap.invariants == m0.iheap.invariants /\
    m1.iname_ctr == m0.iname_ctr /\
    heap_ctr_valid m1.ctr m1.ghost_ctr m1.iname_ctr m1.iheap
  })
  (frame:slprop)
: Lemma
  (requires
    interp ((up fp `star` frame) `star` mem_invariant e m0) m0)
  (ensures (
      let (| x, _ |) = f m0.iheap.concrete in
      interp ((up (fp' x) `star` frame) `star` mem_invariant e m1) m1))
= let h0 = m0.iheap.concrete in
  let (| x, h1 |) = f m0.iheap.concrete in
  star_assoc (up fp) frame (mem_invariant e m0);
  assert (interp (up fp `star` (frame `star` mem_invariant e m0)) m0);
  elim_mem_invariant e m0;
  mem_invariant_eq e m0 m1;
  eliminate exists hl hr.
      idisjoint hl hr /\
      m0.iheap == ijoin hl hr /\
      up fp hl /\
      (frame `star` mem_invariant e m0) hr
  returns 
    interp ((up (fp' x) `star` frame) `star` mem_invariant e m1) m1
  with _ . (
    let pick_frame =
      fun (h:H2.heap) ->
          (frame `star` mem_invariant e m0)
          {hr with concrete = h}
    in
    (* proof of affinity *)
    let _ = 
      introduce forall h0 h1.
          pick_frame h0 /\ H2.disjoint h0 h1
          ==> pick_frame (H2.join h0 h1)
      with (
        introduce _ ==> _
        with _ . (
          let left = { hr with concrete = h0 } in
          let right = { invariants=H0.empty_heap; concrete = h1} in
          assert (idisjoint left right)
        )
      )
    in
    assert (H2.heap_prop_is_affine pick_frame);
    let frm : H2.slprop = H2.as_slprop pick_frame in
    H2.intro_star fp frm hl.concrete hr.concrete;
    assert (H2.interp (fp `H2.star` frm) m0.iheap.concrete);
    h2_action_framing f frm h0;
    assert (H2.interp (fp' x `H2.star` frm) h1);
    H2.elim_star (fp' x) frm h1;
    eliminate exists hl' hr'.
          H2.disjoint hl' hr' /\
          h1 == H2.join hl' hr' /\
          H2.interp (fp' x) hl' /\
          H2.interp frm hr'
    returns _
    with _ . (
      assert (pick_frame hr');
      let ml = { invariants=hl.invariants; concrete=hl'} in
      let mr = {hr with concrete=hr'} in 
      assert ((frame `star` mem_invariant e m0) mr);
      assert ((up (fp' x)) ml);
      assert (idisjoint ml mr);
      assert (H2.join hl' hr' == m1.iheap.concrete);
      assert (m1.iheap == ijoin ml mr);
      star_assoc (up (fp' x)) frame (mem_invariant e m0);
      assert (mem_invariant e m0 == mem_invariant e m1)
    )
  )

let lift_heap_action_aux (#fp:H2.slprop u#a) (#a:Type u#b) (#fp':a -> H2.slprop u#a) (#mut:_)
                     (e:inames)
                     ($f:H2.action #mut #None fp a fp')
: refined_pre_action (mg_of_mut mut) e (up fp) a (fun x -> up (fp' x))
= fun (m0:hmem_with_inv_except e (up fp)) ->
    assert (interp (up fp `star` mem_invariant e m0) m0);
    elim_mem_invariant e m0;
    assert (heap_ctr_valid m0.ctr m0.ghost_ctr m0.iname_ctr m0.iheap);
    let ih0 = m0.iheap in
    let h0 = m0.iheap.concrete in
    assert (H2.interp fp h0);
    let (| x, h1 |) = f m0.iheap.concrete in
    let ih1 = { m0.iheap with concrete = h1 } in
    let m1 = { m0 with iheap = ih1 } in
    assert (H2.is_frame_preserving mut None f);
    elim_h2_frame_preserving f h0;
    assert (heap_ctr_valid m1.ctr m1.ghost_ctr m1.iname_ctr m1.iheap);
    mem_invariant_eq e m0 m1;
    mem_evolves_iff m0 m1;
    assert (mem_evolves m0 m1);
    assert (maybe_ghost_action (mg_of_mut mut) m0 m1);
    let aux (frame:slprop)
    : Lemma 
      (requires
        interp ((up fp `star` frame) `star` mem_invariant e m0) m0)
      (ensures
        interp ((up (fp' x) `star` frame) `star` mem_invariant e m1) m1 /\
        mem_evolves m0 m1 /\
        maybe_ghost_action (mg_of_mut mut) m0 m1)
    = frame_heap_action f e m0 m1 frame
    in
    emp_u (up fp);
    emp_u (up (fp' x));
    aux emp;
    FStar.Classical.(forall_intro (move_requires aux));
    assert (frame_related_mems (up fp) (up (fp' x)) e m0 m1);
    (| x, m1 |)

let lift_heap_action (#fp:H2.slprop u#a) (#a:Type u#b) (#fp':a -> H2.slprop u#a) (#mut:_)
                     (e:inames)
                     ($f:H2.action #mut #None fp a fp')
: tot_action_nf_except (mg_of_mut mut) e (up fp) a (fun x -> up (fp' x))
= refined_pre_action_as_action (lift_heap_action_aux e f)

let change_slprop (#e:inames)
                  (p q:slprop)
                  (proof: (m:mem -> Lemma (requires interp p m) (ensures interp q m)))
: pst_ghost_action_except unit e p (fun _ -> q)
=  let g
     : refined_pre_action true e p unit (fun _ -> q)
     = fun m ->
          assert (interp (p `star` mem_invariant e m) m);
          eliminate exists h0 h1.
              idisjoint h0 h1 /\
              m.iheap == ijoin h0 h1 /\
              p h0 /\
              mem_invariant e m h1
          returns interp (q `star` mem_invariant e m) m
          with _ . (
            let m0 = {m with iheap = h0} in
            let m1 = {m with iheap = h1} in
            proof m0
          );
          let m : hmem_with_inv_except e q = m in
          assert (mem_evolves m m);
          assume (frame_related_mems p q e m m);
          (| (), m |)
   in
   lift_tot_action (refined_pre_action_as_action g)

let witness_h_exists #e #a p =
  fun frame (m0:hmem_with_inv_except e (h_exists p `star` frame)) ->
    assert (interp (h_exists p `star` frame `star` mem_invariant e m0) m0);
    star_assoc (h_exists p) frame (mem_invariant e m0);
    eliminate exists h0 h1.
        idisjoint h0 h1 /\
        m0.iheap == ijoin h0 h1 /\
        h_exists p h0 /\
        (frame `star` mem_invariant e m0) h1
    returns exists x. interp (p x `star` frame `star` mem_invariant e m0) m0
    with _ . (
      assert (exists x. p x h0);
      eliminate exists x.
          p x h0
      returns
        exists x.
          interp (p x `star` frame `star` mem_invariant e m0) m0
      with _ . (
        star_assoc (p x) frame (mem_invariant e m0)
      )
    );
    let x : erased a = 
      FStar.IndefiniteDescription.indefinite_description_tot 
        a 
        (fun x -> interp (p x `star` frame `star` mem_invariant e m0) m0)
    in
    let m : hmem_with_inv_except e (p x `star` frame) = m0 in 
    x, m

let intro_exists #e #a p x =
  fun frame (m0:hmem_with_inv_except e (p x `star` frame)) ->
    assert (interp (p x `star` frame `star` mem_invariant e m0) m0);
    star_assoc (p x) frame (mem_invariant e m0);
    eliminate exists h0 h1.
        idisjoint h0 h1 /\
        m0.iheap == ijoin h0 h1 /\
        p x h0 /\
        (frame `star` mem_invariant e m0) h1
    returns interp (h_exists p `star` frame `star` mem_invariant e m0) m0
    with _ . (
      assert (h_exists p h0);
      star_assoc (h_exists p) frame (mem_invariant e m0)
    );
    let m : hmem_with_inv_except e (h_exists p `star` frame) = m0 in
    (), m

let lift_h_exists #e #a p =
  fun frame (m0:hmem_with_inv_except e (h_exists #a p `star` frame)) -> 
    assert (interp (h_exists #a p `star` frame `star` mem_invariant e m0) m0);
    star_assoc (h_exists #a p) frame (mem_invariant e m0);
    eliminate exists h0 h1.
        idisjoint h0 h1 /\
        m0.iheap == ijoin h0 h1 /\
        h_exists #a p h0 /\
        (frame `star` mem_invariant e m0) h1
    returns interp (h_exists #(U.raise_t a) (U.lift_dom p)
                   `star` frame `star` mem_invariant e m0) m0
    with _ . (
      assert (exists x. p x h0);
      eliminate exists x.
          p x h0
      returns h_exists #(U.raise_t a) (U.lift_dom p) h0
      with _ . (
        let p' = U.lift_dom p in
        assert (p' (U.raise_val x) h0)
      );
      star_assoc (h_exists #(U.raise_t a) (U.lift_dom p)) frame (mem_invariant e m0)
    );
    (), m0

let elim_pure #opened_invariants p = 
  lift_tot_action (lift_heap_action opened_invariants (H2.elim_pure p))

let intro_pure #opened_invariants p pf = 
  lift_tot_action (lift_heap_action opened_invariants (H2.intro_pure p pf))

let drop #e p =
  fun frame (m0:hmem_with_inv_except e (p `star` frame)) ->
    star_assoc p frame (mem_invariant e m0);
    assert (interp (p `star` (frame `star` mem_invariant e m0)) m0);
    assert (interp (frame `star` mem_invariant e m0) m0);
    emp_u (frame `star` mem_invariant e m0);
    star_assoc emp frame (mem_invariant e m0);
    (), m0

let lift_ghost
      (#a:Type)
      #opened_invariants #p #q
      (ni_a:non_info a)
      (f:erased (pst_ghost_action_except a opened_invariants p q))
  : pst_ghost_action_except a opened_invariants p q
  = fun frame m0 ->
      let xm1 : erased (a * full_mem) = 
        let ff = reveal f in
        let x, m1 = ff frame m0 in
        assert (maybe_ghost_action true m0 m1);
        hide (x, m1)
      in
      let m1' : erased full_mem = hide (snd (reveal xm1)) in
      let x' : erased a = hide (fst (reveal xm1)) in
      let iheap =
        { m0.iheap 
            with concrete = H2.upd_ghost_heap m0.iheap.concrete (hide (m1'.iheap.concrete));
                 invariants = m1'.iheap.invariants } in
      let m1 : full_mem = 
        { m0 with iheap;
                  ghost_ctr = (reveal m1').ghost_ctr;
                  iname_ctr = (reveal m1').iname_ctr;
                   } in
      let x = ni_a (hide (fst (reveal xm1))) in
      (x, m1)

(* Concrete small refs *)
let pts_to #a #pcm r v = up (H2.pts_to #a #pcm r v)

let sel_action #a #pcm e r v0
  = lift_tot_action (lift_heap_action e (H2.sel_action #a #pcm r v0))

let upd_action #a #pcm e r v0 v1
  = lift_tot_action (lift_heap_action e (H2.upd_action #a #pcm r v0 v1))

let free_action #a #pcm e r v0
  = lift_tot_action (lift_heap_action e (H2.free_action #a #pcm r v0))

let split_action #a #pcm e r v0 v1
  = lift_tot_action (lift_heap_action e (H2.split_action #a #pcm r v0 v1))

let gather_action #a #pcm e r v0 v1
  = lift_tot_action (lift_heap_action e (H2.gather_action #a #pcm r v0 v1))

// let weaken (p q r:slprop) (h:H.hheap (p `star` q) { H.stronger q r })
//   : H.hheap (p `star` r)
//   = H.weaken p q r h; h

// let weaken_pure (q r: prop)
//   : Lemma
//     (requires (q ==> r))
//     (ensures H.stronger (H.pure q) (H.pure r))
//   = let aux (h:H.heap)
//         : Lemma (ensures (H.interp (H.pure q) h ==> H.interp (H.pure r) h))
//                 [SMTPat ()]
//         = H.pure_interp q h;
//           H.pure_interp r h
//     in
//     ()

// let inc_ctr (#p:slprop) #e (m:hmem_with_inv_except e p)
//   : m':hmem_with_inv_except e p{m'.ctr = m.ctr + 1 /\ H.stronger (linv e m) (linv e m')}
//   = let m' : mem = { m with ctr = m.ctr + 1} in
//     assert (interp (p `star` linv e m) m');
//     assert (linv e m == lock_store_invariant e m.locks
//                         `star`
//                         ctr_validity m.ctr m.ghost_ctr (heap_of_mem m));
//     assert (linv e m' == lock_store_invariant e m.locks
//                          `star`
//                         ctr_validity (m.ctr + 1) m.ghost_ctr (heap_of_mem m));
//     H.weaken_free_above CONCRETE (heap_of_mem m) m.ctr (m.ctr + 1);
//     weaken_pure (heap_ctr_valid m.ctr m.ghost_ctr (heap_of_mem m))
//                 (heap_ctr_valid (m.ctr + 1) m.ghost_ctr (heap_of_mem m));
//     assert (H.stronger
//                   (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m))
//                   (ctr_validity (m.ctr + 1) m.ghost_ctr (heap_of_mem m)));
//     H.star_associative p (lock_store_invariant e m.locks)
//                          (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m));
//     H.stronger_star (lock_store_invariant e m.locks)
//                     (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m))
//                     (ctr_validity (m.ctr + 1) m.ghost_ctr (heap_of_mem m));
//     H.weaken (p `star` lock_store_invariant e m.locks)
//              (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m))
//              (ctr_validity (m.ctr + 1) m.ghost_ctr (heap_of_mem m))
//              (heap_of_mem m');
//     H.star_associative p (lock_store_invariant e m.locks)
//                          (ctr_validity (m.ctr + 1) m.ghost_ctr (heap_of_mem m));
//     let m' : hmem_with_inv_except e p = m' in
//     m'

let with_fresh_counter (#t:Type u#t) (#post:t -> H2.slprop u#a) (e:inames)
  (f: (addr:nat ->
        H2.action #MUTABLE #(Some CONCRETE)
          #(fun h -> h `H2.free_above_addr CONCRETE` addr)
          #(fun h -> h `H2.free_above_addr CONCRETE` (addr + 1))      
          H2.emp 
          t
          post))
: pst_action_except t e emp (fun x -> up (post x))
= admit()
// = let f : refined_pre_action false e emp t post
//     = fun m0 ->
//         let h = hheap_of_hmem m0 in
//         let (|r, h'|) = f m0.ctr h in
//         let m' : hmem_with_inv_except e emp = inc_ctr m0 in
//         let h' : H.hheap (post r `star` linv e m') = weaken _ (linv e m0) (linv e m') h' in
//         let m1 : hmem_with_inv_except e (post r) = hmem_of_hheap m' h' in
//         let aux (frame:slprop)
//           : Lemma
//             (requires
//                interp ((emp `star` frame) `star` linv e m0) m0)
//             (ensures
//                interp ((post r `star` frame) `star` linv e m1) m1 /\
//                mem_evolves m0 m1)
//             [SMTPat (emp `star` frame)]
//           = star_associative emp frame (linv e m0);
//             assert (H.interp (emp `star` (frame `star` linv e m0)) h);
//             assert (H.interp (post r `star` (frame `star` linv e m0)) h');
//             star_associative (post r) frame (linv e m0);
//             assert (H.interp ((post r `star` frame) `star` linv e m0) h');
//             assert (H.stronger (linv e m0) (linv e m'));
//             assert (H.equiv (linv e m') (linv e m1));
//             assert (H.stronger (linv e m0) (linv e m1));
//             let h' : H.hheap ((post r `star` frame) `star` linv e m1) = weaken _ (linv e m0) (linv e m1) h' in
//             assert (H.interp ((post r `star` frame) `star` linv e m1) h')
//         in
//         assert (frame_related_mems emp (post r) e m0 m1);
//         (| r, m1 |)
//     in
//     lift_tot_action (refined_pre_action_as_action f)


let alloc_action #a #pcm e x
  = with_fresh_counter e (H2.extend #a #pcm x)

let select_refine #a #p e r x f
  = lift_tot_action (lift_heap_action e (H2.select_refine #a #p r x f))

let upd_gen #a #p e r x y f
  = lift_tot_action (lift_heap_action e (H2.upd_gen_action r x y f))

let pts_to_not_null_action
      (#a:Type u#a) (#pcm:pcm a)
      (e:inames)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r))) e
    (pts_to r v)
    (fun _ -> pts_to r v)
= lift_tot_action (lift_heap_action e (H2.pts_to_not_null_action #a #pcm r v))

let ghost_ref = H2.ghost_ref
let ghost_pts_to #a #pcm r v = up (H2.ghost_pts_to #a #pcm r v)


// let inc_ghost_ctr (#p:slprop) #e (m:hmem_with_inv_except e p)
//   : m':hmem_with_inv_except e p{reveal m'.ghost_ctr = m.ghost_ctr + 1 /\ H.stronger (linv e m) (linv e m')}
//   = let m' : mem = { m with ghost_ctr = m.ghost_ctr + 1} in
//     assert (interp (p `star` linv e m) m');
//     assert (linv e m == lock_store_invariant e m.locks
//                         `star`
//                         ctr_validity m.ctr m.ghost_ctr (heap_of_mem m));
//     assert (linv e m' == lock_store_invariant e m.locks
//                          `star`
//                         ctr_validity m.ctr (m.ghost_ctr + 1) (heap_of_mem m));
//     H.weaken_free_above GHOST (heap_of_mem m) m.ghost_ctr (m.ghost_ctr + 1);
//     weaken_pure (heap_ctr_valid m.ctr m.ghost_ctr (heap_of_mem m))
//                 (heap_ctr_valid m.ctr (m.ghost_ctr + 1) (heap_of_mem m));
//     assert (H.stronger
//                   (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m))
//                   (ctr_validity m.ctr (m.ghost_ctr + 1) (heap_of_mem m)));
//     H.star_associative p (lock_store_invariant e m.locks)
//                          (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m));
//     H.stronger_star (lock_store_invariant e m.locks)
//                     (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m))
//                     (ctr_validity m.ctr (m.ghost_ctr + 1) (heap_of_mem m));
//     H.weaken (p `star` lock_store_invariant e m.locks)
//              (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m))
//              (ctr_validity m.ctr (m.ghost_ctr + 1) (heap_of_mem m))
//              (heap_of_mem m');
//     H.star_associative p (lock_store_invariant e m.locks)
//                          (ctr_validity m.ctr (m.ghost_ctr + 1) (heap_of_mem m));
//     let m' : hmem_with_inv_except e p = m' in
//     m'
#push-options "--fuel 0 --ifuel 0 --split_queries no --z3rlimit_factor 2"
let with_fresh_ghost_counter (#t:Type u#t) (#post:t -> H2.slprop u#a) (e:inames)
  (f: (addr:erased nat ->
        H2.action #ONLY_GHOST #(Some GHOST)
          #(fun h -> h `H2.free_above_addr GHOST` addr)
          #(fun h -> h `H2.free_above_addr GHOST` (addr + 1))      
          H2.emp 
          t
          post))
: pst_ghost_action_except t e emp (fun x -> up (post x))
= let f : refined_pre_action true e emp t (fun x -> up (post x))
    = fun m0 -> 
        let h0 = m0.iheap.concrete in
        elim_mem_invariant e m0;
        let (|r, h1|) = f m0.ghost_ctr h0 in
        let ih1 = { m0.iheap with concrete = h1 } in
        let m1 = { m0 with iheap = ih1; ghost_ctr = m0.ghost_ctr + 1 } in
        elim_h2_frame_preserving (f m0.ghost_ctr) h0;
        mem_evolves_iff m0 m1;
        assert (mem_evolves m0 m1);
        assert (maybe_ghost_action true m0 m1);
        assert (heap_ctr_valid m1.ctr m1.ghost_ctr m1.iname_ctr m1.iheap);
        let aux (frame:slprop)
          : Lemma
            (requires
               interp ((emp `star` frame) `star` mem_invariant e m0) m0)
            (ensures
               interp ((up (post r) `star` frame) `star` mem_invariant e m1) m1)
            [SMTPat (emp `star` frame)]
          = frame_heap_action (f m0.ghost_ctr) e m0 m1 frame
        in
        emp_u emp;
        emp_u (up (post r));
        aux emp;
        let m1 : hmem_with_inv_except e (up (post r)) = m1 in
        assert (frame_related_mems emp (up (post r)) e m0 m1);
        (| r, m1 |)
    in
    lift_tot_action (refined_pre_action_as_action f)

let ghost_alloc #e #a #pcm x
  = with_fresh_ghost_counter e (H2.ghost_extend #a #pcm x)

let ghost_read #o #a #p r x f
  = lift_tot_action (lift_heap_action o (H2.ghost_read #a #p r x f))
let ghost_write #o #a #p r x y f
  = lift_tot_action (lift_heap_action o (H2.ghost_write #a #p r x y f)) 
let ghost_share #o #a #p r v0 v1
  = lift_tot_action (lift_heap_action o (H2.ghost_share #a #p r v0 v1))
let ghost_gather #o #a #p r v0 v1
  = lift_tot_action (lift_heap_action o (H2.ghost_gather #a #p r v0 v1))

let big_pts_to #a #pcm r v = up (H2.big_pts_to #a #pcm r v)

let big_sel_action #a #pcm e r v0
  = lift_tot_action (lift_heap_action e (H2.big_sel_action #a #pcm r v0))

let big_upd_action #a #pcm e r v0 v1
  = lift_tot_action (lift_heap_action e (H2.big_upd_action #a #pcm r v0 v1))

let big_free_action #a #pcm e r v0
  = lift_tot_action (lift_heap_action e (H2.big_free_action #a #pcm r v0))

let big_split_action #a #pcm e r v0 v1
  = lift_tot_action (lift_heap_action e (H2.big_split_action #a #pcm r v0 v1))

let big_gather_action #a #pcm e r v0 v1
  = lift_tot_action (lift_heap_action e (H2.big_gather_action #a #pcm r v0 v1))

let big_alloc_action #a #pcm e x
  = with_fresh_counter e (H2.big_extend #a #pcm x)

let big_select_refine #a #p e r x f
  = lift_tot_action (lift_heap_action e (H2.big_select_refine #a #p r x f))

let big_upd_gen #a #p e r x y f
  = lift_tot_action (lift_heap_action e (H2.big_upd_gen_action r x y f))

let big_pts_to_not_null_action
      (#a:Type u#(ua + 1)) (#pcm:pcm a)
      (e:inames)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r))) e
    (big_pts_to r v)
    (fun _ -> big_pts_to r v)
= lift_tot_action (lift_heap_action e (H2.big_pts_to_not_null_action #a #pcm r v))


let big_ghost_pts_to #a #pcm r v = up (H2.big_ghost_pts_to #a #pcm r v)
let big_ghost_alloc #e #a #pcm x
  = with_fresh_ghost_counter e (H2.big_ghost_extend #a #pcm x)
let big_ghost_read #o #a #p r x f
  = lift_tot_action (lift_heap_action o (H2.big_ghost_read #a #p r x f))
let big_ghost_write #o #a #p r x y f
  = lift_tot_action (lift_heap_action o (H2.big_ghost_write #a #p r x y f)) 
let big_ghost_share #o #a #p r v0 v1
  = lift_tot_action (lift_heap_action o (H2.big_ghost_share #a #p r v0 v1))
let big_ghost_gather #o #a #p r v0 v1
  = lift_tot_action (lift_heap_action o (H2.big_ghost_gather #a #p r v0 v1))

