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


let raw_inv_store : Type u#(a + 3) = erased (H0.heap u#(a + 2))

(** [sel] is a ghost read of the value contained in a heap reference *)
noeq
type cell : Type u#(a + 1) =
  | Ref : a:Type u#a ->
          p:pcm a ->
          frac:Frac.perm{ frac `Frac.lesser_equal_perm` Frac.full_perm } ->
          v:a { frac == Frac.full_perm ==> p.refine v } ->
          cell

assume
val sel (i:nat) (m:H0.heap u#a) : option (cell u#a)

assume
val sel_empty (i:nat)
  : Lemma 
    (ensures sel i H0.empty_heap == None)
    [SMTPat (sel i H0.empty_heap)
    ]

module PA = PulseCore.PCM.Agreement

let inv_store_has_only_invs (l:raw_inv_store u#a) : prop =
  forall i.
    match sel i l with
    | None -> True
    | Some cell ->
      let Ref a p f v = cell in
      a == PA.agreement H2.slprop /\
      p == PA.pcm_agreement #H2.slprop
  
let istore = raw_inv_store

// let join_istore (h0 h1:istore)
//   : Lemma 
//     (requires H0.disjoint h0 h1)
//     (ensures (inv_store_has_only_invs (H0.join h0 h1)))
//     [SMTPat ((inv_store_has_only_invs (H0.join h0 h1)))]
//   = admit()

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
  = admit() //H2.h2_join_empty h

let h0_join_empty (h:H0.heap)
  : Lemma (H0.disjoint h H0.empty_heap /\
           H0.join h H0.empty_heap == h)
           [SMTPatOr
              [[SMTPat (H0.disjoint h H0.empty_heap)];
               [SMTPat (H0.join h H0.empty_heap)]]]
  = H0.join_empty h

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

let down (p:slprop) : big_slprop =
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

let emp_unit p = admit()
let pure_equiv p q = H2.pure_equiv p q
val pure_interp (q:prop) (m:mem) 
  : Lemma (interp (pure q) m <==> q)
          [SMTPat (interp (pure q) m)]
let pure_interp q m = H2.pure_interp q (heap_of_mem m).concrete
let pure_true_emp () : Lemma (pure True `equiv` emp) =
  admit()


////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////
let star_commutative (p1 p2:slprop) = admit()

let star_associative (p1 p2 p3:slprop) = admit()

let star_congruence (p1 p2 p3 p4:slprop) =
  slprop_extensionality p1 p3;
  slprop_extensionality p2 p4

let small_star_congruence (p1 p2:vprop u#a)
: Lemma (is_small (p1 `star` p2))
= admit()

let small_exists_congruence (#a:Type u#a) (p:a -> slprop u#b)
: Lemma
    (requires forall x. is_small (p x))
    (ensures is_small (h_exists p))
= admit()

val affine_star (p q:slprop) (m:mem)
  : Lemma ((interp (p `star` q) m ==> interp p m /\ interp q m))

let affine_star (p q:slprop) (m:mem) = ()

////////////////////////////////////////////////////////////////////////////////
// Invariants
////////////////////////////////////////////////////////////////////////////////

let iname = nat
module W = FStar.Witnessed.Core
let sl_pure_imp (p:prop) (q: squash p -> slprop) : slprop =
  as_slprop (fun (h:iheap) -> p ==> q () h)

let cell_pred_pre (c:cell) =
  let Ref a pcm _ _ = c in
  a == PA.agreement H2.slprop /\
  pcm == PA.pcm_agreement #H2.slprop

let cell_pred_post (c:cell) (_:squash (cell_pred_pre c)) =
  let Ref _ _ _ v = c in
  let v : PA.agreement H2.slprop = v in
  match v with
  | None -> emp
  | Some p -> up p


let invariant_of_one_cell (addr:nat) (e:inames) (l:istore u#a) : slprop u#a =
  if addr `S.mem` e then emp
  else match sel addr l with
       | Some c -> 
         sl_pure_imp 
          (cell_pred_pre c)
          (cell_pred_post c)
       | _ -> emp

let rec istore_invariant_aux
         (from:nat) (down_to:nat { down_to <= from})
         (e:inames) (l:istore u#a) : slprop u#a =
  invariant_of_one_cell from e l `star` 
  (if from = down_to then emp else istore_invariant_aux (from - 1) down_to e l)

let istore_invariant from e l = istore_invariant_aux from 0 e l

let istore_evolves : FStar.Preorder.preorder istore =
  fun (l1 l2 : istore) ->
    forall addr. Some? (sel addr l1) ==> sel addr l1 == sel addr l2

let inames_in (e:inames) (l:istore) : prop = 
  forall i. Set.mem i e ==> Some? (sel i l)

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
    //m0.ctr <= m1.ctr /\
    istore_evolves m0.iheap.invariants m1.iheap.invariants

let frame_related_mems (fp0 fp1:slprop u#a) e (m0:hmem_with_inv_except e fp0) (m1:hmem_with_inv_except e fp1) =
    forall (frame:slprop u#a).
      interp ((fp0 `star` frame) `star` mem_invariant e m0) m0 ==>
      interp ((fp1 `star` frame) `star` mem_invariant e m1) m1 /\
      mem_evolves m0 m1

let iname_for_p (i:iname) (p:slprop) (m:istore) =
  match sel i m with
  | None -> False
  | Some cell ->
    let Ref a pcm _ v = cell in
    a == PA.agreement H2.slprop /\
    pcm == PA.pcm_agreement #H2.slprop /\ (
    let v : PA.agreement H2.slprop = cell.v in
    match v with
    | None -> False
    | Some q -> up q == p
    )

assume
val core_ref_of_iname (i:iname) : H0.core_ref

let h0_of_slprop (p:H0.slprop u#(a + 2)) : H0.a_heap_prop u#(a + 2) =
  H0.interp_depends_only_on p;
  fun h -> H0.interp p h

let lift_h0 (p:H0.slprop u#(a + 2))
: slprop u#a
= as_slprop (fun h -> h0_of_slprop p h.invariants)

let i_pts_to_p (i:iname) (p:slprop u#a) : H0.slprop u#(a + 2) =
    H0.pts_to 
      #_
      #(PA.pcm_agreement #H2.slprop)
      (core_ref_of_iname i)
      (Some (down p))

let ( -~- ) (i:iname) (p:slprop u#a)
  : slprop u#a
  = lift_h0 (i_pts_to_p i p)

let set_add (i:iname) (s:inames) = Set.union (Set.singleton i) s

let star_comm (p1 p2:slprop)
  : Lemma ((p1 `star` p2) == (p2 `star` p1))
  = star_commutative p1 p2;
    slprop_extensionality (p1 `star` p2) (p2 `star` p1)

let star_assoc (p q r:slprop)
  : Lemma (p `star` (q `star` r) == (p `star` q) `star` r)
  = star_associative p q r;
    slprop_extensionality (p `star` (q `star` r)) ((p `star` q) `star` r)

let emp_u (p:slprop) : Lemma (p == p `star` emp) = emp_unit p; slprop_extensionality p (p `star` emp)

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
          (down_to:nat{from >= down_to})
          (e:inames)
          (e':inames { forall i. i `Set.mem` e' ==> from < i \/ i < down_to })
          (l:istore)
: Lemma
  (ensures istore_invariant_aux from down_to e l == istore_invariant_aux from down_to (Set.union e' e) l)
  (decreases from)
= if from = down_to
  then ()
  else weaken_inames_istore_invariant (from - 1) down_to e e' l

let sl_pure_imp_elim (p:prop) (q: squash p -> slprop)
  : Lemma (p ==> sl_pure_imp p q == q ())
  = admit()

let rec move_invariant (e:inames) (l:istore) (p:slprop) (from:nat)
                       (i:iname{iname_for_p i p l /\ from >= i /\ ~(i `Set.mem` e)})
: Lemma (ensures 
               (istore_invariant from e l) ==
               (p `star` istore_invariant from (set_add i e) l))
        (decreases from)
= calc (==) {
    istore_invariant from e l;
    (==) {}
    istore_invariant_aux from 0 e l;
    (==) {}
    invariant_of_one_cell from e l `star` (if from = 0 then emp else (istore_invariant_aux (from - 1) 0 e l));
  };
  if i = from
  then (
    let Some c = sel i l in
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
        istore_invariant_aux from 0 (set_add i e) l;
      (==) {}
        invariant_of_one_cell from (set_add i e) l `star` (istore_invariant_aux (from - 1) 0 (set_add i e) l);
      (==) {}
        emp `star` (istore_invariant_aux (from - 1) 0 (set_add i e) l);
      (==) { star_comm emp (istore_invariant_aux (from - 1) 0 (set_add i e) l) }
        istore_invariant_aux (from - 1) 0 (set_add i e) l `star` emp;
      (==) { emp_u (istore_invariant_aux (from - 1) 0 (set_add i e) l)}
        istore_invariant_aux (from - 1) 0 (set_add i e) l;
      (==) { weaken_inames_istore_invariant (from - 1) 0 e (Set.singleton i) l }
        istore_invariant (from - 1) e l;
      }
    )
  )
  else (
    move_invariant e l p (from - 1) i;
    calc (==) {
      istore_invariant from e l;
    (==) {}
      invariant_of_one_cell from e l `star` (p `star` istore_invariant_aux (from - 1) 0 (set_add i e) l);
    (==) { _ by (T.mapply (`pqr_qpr))}
      p `star` (invariant_of_one_cell from e l `star` istore_invariant_aux (from - 1) 0 (set_add i e) l);
    (==) { }
      p `star` (invariant_of_one_cell from (set_add i e) l `star` istore_invariant_aux (from - 1) 0 (set_add i e) l);
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
  = let aux (frame:slprop) (m0:hmem_with_inv_except e (fp `star` frame))
        : Lemma
          (ac_reasoning_for_m_frame_preserving fp frame (mem_invariant e m0) m0;
            let (| x, m1 |) = f m0 in
            interp ((fp' x `star` frame) `star` mem_invariant e m1) m1 /\
            mem_evolves m0 m1)
        = ac_reasoning_for_m_frame_preserving fp frame (mem_invariant e m0) m0;
          let (| x, m1 |) = f m0 in
          assert (interp (fp' x `star` mem_invariant e m1) m1);
          assume (interp ((fp' x `star` mem_invariant e m1) `star` frame) m1);
          pqr_prq (fp' x) (mem_invariant e m1) frame;
          assert (interp ((fp' x `star` frame) `star` mem_invariant e m1) m1);
          assert (mem_evolves m0 m1)
    in
    emp_u fp;
    assert (interp (fp `star` mem_invariant e m0) m0);
    assert (interp ((fp `star` emp) `star` mem_invariant e m0) m0);
    aux emp m0

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
  = admit()
let iname_ref = erased (H0.ref _ (PA.pcm_agreement #H2.slprop))
let iname_ref_pts_to (i:iname_ref) (p:slprop) = lift_h0 (H0.pts_to i (Some (down p)))

let lift_h0_pred (pre:H0.heap -> prop)
  : iheap -> prop
  = fun h -> pre h.invariants

let star_congruence_h0 (p q:H0.slprop)
  : Lemma (lift_h0 (p `H0.star` q) == lift_h0 p `star` lift_h0 q)
  = admit()

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

let new_invariant_pre_action (e:inames) (p:slprop { is_big p })
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
      : erased (x:H0.ref _ _ & H0.full_hheap (H0.pts_to x (Some (down p))))
      = H0.intro_emp m0.iheap.invariants;
        Ghost.hide <| H0.extend #_ #(PA.pcm_agreement) (Some (down p)) iname m0.iheap.invariants
    in
    let x : iname_ref = dfst res in
    let inv1 : raw_inv_store (* erased (H0.full_hheap (H0.pts_to x (Some (down p)))) *) = dsnd res in
    (* Need a lemma about extend from H0 *)
    assume (forall i. i < iname ==> sel i m0.iheap.invariants == sel i inv1);
    assume (sel iname inv1 == Some (Ref _ (PA.pcm_agreement #H2.slprop) Frac.full_perm (Some (down p))));
    assume (forall i. i > iname ==> sel i inv1 == None);
    // assert (inv_store_has_only_invs (reveal inv1));
    let iheap1 = { m0.iheap with invariants = inv1 } in
    let m1 = { m0 with iname_ctr = iname + 1; iheap = iheap1 } in
    assert (full_mem_pred m1);
    assert (heap_ctr_valid m1.ctr m1.ghost_ctr m1.iname_ctr m1.iheap);
    (* Induction on istore_invariant, given the assumes above about how invs have changed *)    
    assume (istore_invariant m1.iname_ctr e m1.iheap.invariants ==
            up (down p) `star` istore_invariant m0.iname_ctr e m0.iheap.invariants);
    assert (up (down p) == p);
    assert (istore_invariant m1.iname_ctr e m1.iheap.invariants ==
            p `star` istore_invariant m0.iname_ctr e m0.iheap.invariants);
    assert (interp (istore_invariant m1.iname_ctr e m1.iheap.invariants) m0);
    (* istore_invariants is a lifting of a conjunction of ups; so, since m0.iheap.concrete didn't change, this should hold *)
    assume (interp (istore_invariant m1.iname_ctr e m1.iheap.invariants) m1);
    intro_pure_star
      (istore_invariant m1.iname_ctr e m1.iheap.invariants)
      (heap_ctr_valid m1.ctr m1.ghost_ctr m1.iname_ctr m1.iheap)
      m1;
    assert (interp (mem_invariant e m1) m1);
    assert (H0.interp (H0.pts_to x (Some (down p))) m1.iheap.invariants);
    assume (interp (iname_ref_pts_to x p `star` mem_invariant e m1) m1);
    assume (inames_ok e m1);
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
        (* todo: proof of affinity *)
        assume (H0.heap_prop_is_affine pick_frame);
        assert (pick_frame m0.iheap.invariants);
        let frm : H0.slprop = H0.as_slprop pick_frame in
        assert(H0.interp frm m0.iheap.invariants);
        (* easy, intro emp *)
        assume (H0.interp (H0.emp `H0.star` frm) m0.iheap.invariants);
        let inv0 : H0.full_hheap (H0.emp `H0.star` frm) = m0.iheap.invariants in
        H0.action_framing 
          (H0.extend #_ #(PA.pcm_agreement) (Some (down p)) iname)
          frm
          inv0;
        assert (H0.interp (H0.pts_to x (Some (down p)) `H0.star` frm)
                          inv1);
        assert (interp 
          (lift_h0 
            (H0.pts_to x (Some (down p)) `H0.star` frm))
          m1);
        star_congruence_h0 (H0.pts_to x (Some (down p))) frm;
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
            assume (pick_frame h1_1.invariants);
            let m1_0 = { m1 with iheap = { concrete = H2.empty_heap; invariants = h1_0.invariants } } in
            assert (interp (iname_ref_pts_to x p) m1_0);
            let m1_1 = { m1 with iheap = {m1.iheap with invariants=h1_1.invariants}} in
            assert (interp ((p `star` frame) `star` mem_invariant e m0) m1_1); 
            assume ((p `star` frame) `star` mem_invariant e m0 ==
                    frame `star` (p `star` mem_invariant e m0));
            assume (p `star` mem_invariant e m0 == mem_invariant e m1);
            assert (interp (frame `star` mem_invariant e m1) m1_1);
            assert (disjoint m1_0 m1_1);
            assert (m1 == join m1_0 m1_1);
            intro_star (iname_ref_pts_to x p) (frame `star` mem_invariant e m1) m1_0 m1_1;
            assert (interp (iname_ref_pts_to x p `star` (frame `star` mem_invariant e m1)) m1);
            star_assoc (iname_ref_pts_to x p) frame (mem_invariant e m1)
          );
        assert (H2.heap_evolves m0.iheap.concrete m1.iheap.concrete);
        assume (istore_evolves m0.iheap.invariants m1.iheap.invariants);
        assume (mem_evolves m0 m1)
    in
    assert (frame_related_mems p (iname_ref_pts_to x p) e m0 m1);
    res
  

let new_invariant' (e:inames) (p:slprop)
: pst_ghost_action_except iname e p (fun i -> i -~- p)
= lift_tot_action (refined_pre_action_as_action (new_invariant_pre_action e p))

let new_invariant_tot_action (e:inames) (p:slprop) (m0:hmem_with_inv_except e p{ e `inames_in` m0.locks })
  : Pure (iname & hmem_with_inv_except e emp)
         (requires True)
         (ensures fun (i, m1) ->
           iname_for_p_mem i p m1 /\
           frame_related_mems p emp e m0 m1 /\
           mem_evolves m0 m1)
  = let (| i, l1 |) = extend_lock_store e m0.locks p in
    let m1 = { m0 with locks = l1 } in
    assert (lock_store_invariant e m1.locks ==
            p `star` lock_store_invariant e m0.locks);
    calc (equiv) {
      linv e m1;
        (equiv) {}
      (lock_store_invariant e m1.locks
        `star`
       ctr_validity m1.ctr m1.ghost_ctr (heap_of_mem m1));
        (equiv) {}
      ((p `star` lock_store_invariant e m0.locks)
        `star`
       ctr_validity m1.ctr m1.ghost_ctr (heap_of_mem m1));
        (equiv) {
          H.star_associative p (lock_store_invariant e m0.locks) (ctr_validity m1.ctr m1.ghost_ctr (heap_of_mem m1))
         }
      (p `star` (lock_store_invariant e m0.locks
        `star`
       ctr_validity m1.ctr m1.ghost_ctr (heap_of_mem m1)));
        (equiv) { }
      (p `star` linv e m0);
    };
    assert (iname_for_p_mem i p m1);
    assert (lock_store_evolves m0.locks l1);
    assert (mem_evolves m0 m1);
    hmem_with_inv_equiv e m0 p;
    assert (interp (p `star` lock_store_invariant e m0.locks) m1);
    assert (interp (lock_store_invariant e m1.locks) m1);
    H.emp_unit (lock_store_invariant e m1.locks);
    H.star_commutative (lock_store_invariant e m1.locks) emp;
    assert (interp (emp `star` lock_store_invariant e m1.locks) m1);
    hmem_with_inv_equiv e m1 emp;
    let m1 : hmem_with_inv_except e emp = m1 in
    let aux (frame:slprop)
      : Lemma
        (requires interp ((p `star` frame) `star` linv e m0) m0)
        (ensures interp ((emp `star` frame) `star` linv e m1) m1 /\
                 mem_evolves m0 m1 /\
                 (forall (mp:mprop frame). mp (core_mem m0) <==> mp (core_mem m1)))
        [SMTPat (p `star` frame)]
      = assert (interp ((p `star` frame) `star` linv e m0) m1);
        calc (equiv) {
          ((p `star` frame) `star` linv e m0);
            (equiv) {
                      H.star_commutative p frame;
                      H.star_congruence (p `star` frame) (linv e m0) (frame `star` p) (linv e m0);
                      H.star_associative frame p (linv e m0)
                    }
          (frame `star` (p `star` linv e m0));
            (equiv) {
                      H.star_congruence frame (p `star` linv e m0) frame (linv e m1)
                    }
          (frame `star` linv e m1);
            (equiv) {
                       H.emp_unit (frame `star` linv e m1);
                       H.star_commutative (frame `star` linv e m1) emp;
                       H.star_associative emp frame (linv e m1)
                    }
          ((emp `star` frame) `star` linv e m1);
        };
        assert (interp ((emp `star` frame) `star` linv e m1) m1)
    in
    assert (frame_related_mems p emp e m0 m1);
    ( i, m1 )

let name_is_ok (i:iname) (m0:full_mem u#a) : prop = i < List.Tot.length m0.locks

let witnessed_name_is_ok (i:iname) = W.witnessed (full_mem u#a) mem_evolves (name_is_ok i)



let pre_inv_aux (p:slprop u#a) : Type0 = i:erased iname & witnessed_name_is_ok u#a i
let inv (p:slprop u#a) = i:erased iname & witnessed_name_is_ok u#a i & (i >--> p)

let pre_inv_of_inv (#p:slprop u#a) (i:inv p) : pre_inv u#a = let (|i, w, _|) = i in (|i,w|)
let name_of_pre_inv (i:pre_inv) = dfst i

let rec recall_all (ctx:list (pre_inv u#a))
  : MSTTotal.mst #(full_mem u#a) mem_evolves unit 
    (requires fun _ -> True)
    (ensures fun m0 _ m1 -> m0==m1 /\ (forall (i:pre_inv u#a). i `List.Tot.memP` ctx ==> name_is_ok (name_of_pre_inv i) m0))
  = match ctx with
    | [] -> MST.weaken <| MST.return ()
    | hd::tl ->
      let (| q, i |) = hd in
      let i : W.witnessed (full_mem u#a) mem_evolves (name_is_ok q) = i in
      MST.weaken <|
      MST.bind (MST.recall (name_is_ok q) i) (fun _ -> recall_all u#a tl)

let distinct_invariants_have_distinct_names
      (e:inames)
      (p:slprop u#a)
      (q:slprop u#a { p =!= q })
      (i:inv p)
      (j:inv q)
      (frame:slprop u#a)
: _MstTot (squash (name_of_inv i =!= name_of_inv j)) e (emp u#a) (fun _ -> emp u#a) frame
= let (| ni, wi, toki |) = i in
  let (| nj, wj, tokj |) = j in
  let toki : (ni >--> p) = toki in
  let tokj : (nj >--> q) = tokj in
  let elim 
    : _mst_tot_aux
        (squash (name_of_inv i =!= name_of_inv j))
        e
        emp
        (fun _ -> emp)
        frame
        (fun _ -> name_of_inv i =!= name_of_inv j)
    = fun m0 -> MST.weaken <| MST.return ()
  in
  MST.weaken <|
  MST.bind (MST.recall _ toki) (fun _ ->
  MST.bind (MST.recall _ tokj) (fun _ ->
            with_get_aux elim))

let invariant_name_identifies_invariant
      (e:inames)
      (p:slprop)
      (q:slprop)
      (i:inv p)
      (j:inv q { name_of_inv i == name_of_inv j })
      (frame:slprop)
: _MstTot (squash (p == q /\ i == j)) e emp (fun _ -> emp) frame
= let (| ni, wi, toki |) = i in
  let (| nj, wj, tokj |) = j in
  assert (ni == nj);
  let elim 
    : _mst_tot_aux
        (squash (p == q /\ i == j))
        e
        emp
        (fun _ -> emp)
        frame
        (fun m -> iname_for_p_mem ni p m /\ iname_for_p_mem nj q m)
    = fun _ -> 
        W.witnessed_proof_irrelevant _ _ _ wi wj;
        W.witnessed_proof_irrelevant _ _ _ toki tokj;
        MST.weaken <| MST.return ()
  in
  MST.weaken <|
  MST.bind (MST.recall _ toki) (fun _ ->
  MST.bind (MST.recall _ tokj) (fun _ ->
            with_get_aux elim))
  
let fresh_invariant (e:inames) (p:slprop u#a) (ctx:list (pre_inv u#a)) (frame:slprop u#a)
  : _MstTot (i:inv p { fresh_wrt ctx (name_of_inv i)}) e p (fun _ -> emp u#a) frame
  = let elim
    : _mst_tot_aux
        (i:inv p { fresh_wrt ctx (name_of_inv i)})
        e
        p
        (fun _ -> emp)
        frame
        (fun m0 -> 
          (forall i. i `List.Tot.memP` ctx ==> name_is_ok (name_of_pre_inv i) m0))
    = fun m0 ->
        ac_reasoning_for_m_frame_preserving p frame (locks_invariant e m0) m0;
        assert (interp (p `star` locks_invariant e m0) m0);
        let r = new_invariant_tot_action e p m0 in
        let ( i, m1 ) = r in
        assert (i == List.Tot.length m0.locks);
        assert (not (Set.mem i e));
        assert (mem_evolves m0 m1);
        iname_for_p_stable i p;
        MST.weaken <|
        MST.bind (MSTTotal.put #full_mem #mem_evolves m1) (fun _ ->
        MST.bind (MST.witness #full_mem #mem_evolves (iname_for_p_mem i p)) (fun w ->
        MST.bind (MST.witness #full_mem #mem_evolves (name_is_ok i)) (fun w0 ->
        let i : inv p = (| hide i, w0, w |) in
        assert (fresh_wrt ctx (name_of_inv i));
        MST.weaken #_ #_ #(i:inv p {fresh_wrt ctx (name_of_inv i)})
          #_ #_
          #(fun m0 -> True)
          #(fun m0 _ m1 -> m0==m1)
          <| MST.return i)))
    in
    MST.weaken <|
    MST.bind (recall_all ctx) (fun _ -> with_get_aux elim)

let new_invariant (e:inames) (p:slprop) (frame:slprop)
  : _MstTot (inv p) e p (fun _ -> emp) frame
  = fresh_invariant e p [] frame

let rearrange_invariant (p q r : slprop) (q0 q1:slprop)
  : Lemma
    (requires q `equiv` (q0 `star` q1))
    (ensures  (p `star` (q `star` r)) `equiv`
              ((q0 `star` p) `star` (q1 `star` r)))
  = calc (equiv)
    {
       p `star` (q `star` r);
         (equiv)
           {
             calc (equiv)
             {
               (q `star` r);
                 (equiv) {
                             star_congruence q r (q0 `star` q1) r
                         }
               (q0 `star` q1) `star` r;
             };
             star_congruence p (q `star` r) p ((q0 `star` q1) `star` r)
           }
       (p `star` ((q0 `star` q1) `star` r));
          (equiv) {
                    star_associative q0 q1 r;
                    star_congruence p ((q0 `star` q1) `star` r)
                                    p (q0 `star` (q1 `star` r));
                    star_associative p q0 (q1 `star` r)
                  }
       (p `star` q0) `star` (q1 `star` r);
          (equiv) {
                     star_commutative p q0;
                     star_congruence (p `star` q0) (q1 `star` r)
                                     (q0 `star` p)  (q1 `star` r)
                  }
       (q0 `star` p) `star` (q1 `star` r);
    }

let preserves_frame_invariant (fp fp':slprop)
                              (opened_invariants:inames)
                              (p:slprop)
                              (i:inv p{not (mem_inv opened_invariants i)})
                              (m0:hmem_with_inv_except (add_inv opened_invariants i) (p `star` fp))
                              (m1:mem)
    : Lemma
      (requires preserves_frame (set_add (name_of_inv i) opened_invariants) (p `star` fp) (p `star` fp') m0 m1 /\
                interp (fp' `star` linv opened_invariants m1) m1 /\
                inames_ok opened_invariants m1 /\
                (lock_store_invariant opened_invariants m0.locks `equiv`
                   (p `star` lock_store_invariant (set_add (name_of_inv i) opened_invariants) m0.locks)) /\
                (lock_store_invariant opened_invariants m1.locks `equiv`
                 (p `star` lock_store_invariant (set_add (name_of_inv i) opened_invariants) m1.locks)))
      (ensures  preserves_frame opened_invariants fp fp' m0 m1)
    =
      let aux (frame:slprop)
        : Lemma
           (requires
             interp ((fp `star` frame) `star` linv opened_invariants m0) m0)
           (ensures
             interp ((fp' `star` frame) `star` linv opened_invariants m1) m1 /\
             (forall (f_frame:mprop frame). f_frame (core_mem m0) == f_frame (core_mem m1)))
           [SMTPat()]
        = rearrange_invariant (fp `star` frame) (lock_store_invariant opened_invariants m0.locks) (ctr_validity m0.ctr m0.ghost_ctr (heap_of_mem m0))
                                                p (lock_store_invariant (set_add (name_of_inv i) opened_invariants) m0.locks);
          assert (interp ((p `star` (fp `star` frame)) `star` linv (set_add (name_of_inv i) opened_invariants) m0) m0);
          star_associative p fp frame;
          star_congruence (p `star` (fp `star` frame)) (linv (set_add (name_of_inv i) opened_invariants) m0)
                          ((p `star` fp) `star` frame)  (linv (set_add (name_of_inv i) opened_invariants) m0);
          assert (interp (((p `star` fp) `star` frame) `star` linv (set_add (name_of_inv i) opened_invariants) m0) m0);
          assert (interp (((p `star` fp') `star` frame) `star` linv (set_add (name_of_inv i) opened_invariants) m1) m1);
          star_associative p fp' frame;
          star_congruence ((p `star` fp') `star` frame) (linv (set_add (name_of_inv i) opened_invariants) m1)
                          (p `star` (fp' `star` frame)) (linv (set_add (name_of_inv i) opened_invariants) m1);
          assert (interp ((p `star` (fp' `star` frame)) `star` linv (set_add (name_of_inv i) opened_invariants) m1) m1);
          rearrange_invariant (fp' `star` frame) (lock_store_invariant opened_invariants m1.locks) (ctr_validity m1.ctr m1.ghost_ctr (heap_of_mem m1))
                                                 p (lock_store_invariant (set_add (name_of_inv i) opened_invariants) m1.locks);
          assert (interp ((fp' `star` frame) `star` linv opened_invariants m1) m1);
          ()
      in
      ()


let equiv_ext_right (p q r:slprop)
  : Lemma
      (requires q `equiv` r)
      (ensures (p `star` q) `equiv` (p `star` r))
  = calc (equiv) {
      p `star` q;
         (equiv) { star_commutative p q }
      q `star` p;
         (equiv) { slprop_extensionality q r }
      r `star` p;
         (equiv) { star_commutative p r }
      p `star` r;
    }

let with_inv_helper (fp frame ls1 ctr p ls2:slprop)
  : Lemma
      (requires ls1 `equiv` (p `star` ls2))
      (ensures
        (fp `star` frame `star` (ls1 `star` ctr)) `equiv`
        (p `star` fp `star` frame `star` (ls2 `star` ctr)))
  = calc (equiv) {
      ls1 `star` ctr;
         (equiv) { slprop_extensionality ls1 (p `star` ls2) }
      p `star` ls2 `star` ctr;
    };
    calc (equiv) {
      p `star` ls2 `star` ctr;
         (equiv) { star_associative p ls2 ctr }
      p `star` (ls2 `star` ctr);
    };
    calc (equiv) {
      fp `star` frame `star` p;
         (equiv) { star_commutative (fp `star` frame) p }
      p `star` (fp `star` frame);
         (equiv) { star_associative p fp frame }
      p `star` fp `star` frame;
    };
    calc (equiv) {
      fp `star` frame `star` (ls1 `star` ctr);
         (equiv) { equiv_ext_right (fp `star` frame)
                     (ls1 `star` ctr)
                     (p `star` ls2 `star` ctr) }
      (fp `star` frame) `star` (p `star` ls2 `star` ctr);
         (equiv) { equiv_ext_right (fp `star` frame)
                     (p `star` ls2 `star` ctr)
                     (p `star` (ls2 `star` ctr)) }
      (fp `star` frame) `star` (p `star` (ls2 `star` ctr));
         (equiv) { star_associative (fp `star` frame) p (ls2 `star` ctr) }
      (fp `star` frame `star` p) `star` (ls2 `star` ctr);
         (equiv) { slprop_extensionality
                     (fp `star` frame `star` p)
                     (p `star` fp `star` frame)
                  }
                  
      (p `star` fp `star` frame) `star` (ls2 `star` ctr);
    }

let token_of_inv #p (i:inv p) : (name_of_inv i >--> p) = let (| _, _, tok |) = i in tok

let mst_aux #s rel a p q = x:s { p x } -> MST.mst #s rel a (fun s0 -> s0 == x) q

let with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#opened_invariants:inames)
                   (#p:slprop)
                   (i:inv p{not (mem_inv opened_invariants i)})
                   (f:action_except a (add_inv opened_invariants i) (p `star` fp) (fun x -> p `star` fp' x))
                   (frame:slprop)
  : _MstTot a opened_invariants fp fp' frame
  = let k1 (r:a)
       : MST.mst_aux mem_evolves a
          (fun m1 ->
             inames_ok (set_add (name_of_inv i) opened_invariants) m1 /\
             interp (p `star` fp' r `star` frame `star` locks_invariant (set_add (name_of_inv i) opened_invariants) m1) m1)
          (fun _ x m1 ->
             inames_ok opened_invariants m1 /\
             interp (fp' x `star` frame `star` locks_invariant opened_invariants m1) m1)
      = fun m1 ->
          assert (interp (p `star` fp' r `star` frame `star` locks_invariant (set_add (name_of_inv i) opened_invariants) m1) m1);
          assert (interp (p `star` fp' r `star` frame `star`
          (lock_store_invariant (set_add (name_of_inv i) opened_invariants) m1.locks `star`
            ctr_validity m1.ctr m1.ghost_ctr (heap_of_mem m1))) m1);

          let k2
            : MST.mst_aux mem_evolves a
                (fun m1 ->
                  inames_ok (set_add (name_of_inv i) opened_invariants) m1 /\
                  interp (p `star` fp' r `star` frame `star`
                            (lock_store_invariant (set_add (name_of_inv i) opened_invariants) m1.locks `star`
                              ctr_validity m1.ctr m1.ghost_ctr (heap_of_mem m1))) m1 /\
                  iname_for_p_mem (name_of_inv i) p m1)
                (fun _ x m1 ->
                  inames_ok opened_invariants m1 /\
                  interp (fp' x `star` frame `star` locks_invariant opened_invariants m1) m1)
            = fun m1 ->
                  move_invariant opened_invariants m1.locks p (name_of_inv i);
                  assert (lock_store_invariant opened_invariants m1.locks `equiv`
                      (p `star` lock_store_invariant (set_add (name_of_inv i) opened_invariants) m1.locks));

                  with_inv_helper
                    (fp' r)
                    frame
                    (lock_store_invariant opened_invariants m1.locks)
                    (ctr_validity m1.ctr m1.ghost_ctr (heap_of_mem m1))
                    p
                    (lock_store_invariant (set_add (name_of_inv i) opened_invariants) m1.locks);

                  assert (interp (fp' r `star` frame `star` locks_invariant opened_invariants m1) m1);

                  assert (inames_ok opened_invariants m1);
                  MST.weaken <| MST.return r
          in
          MST.weaken <|
          MST.bind (MST.recall _ (token_of_inv i)) (fun _ -> MST.with_get k2)
      in
    let k0
    : _mst_tot_aux a opened_invariants fp fp' frame
          (iname_for_p_mem (name_of_inv i) p)
    = fun m0 -> 
        assert (iname_for_p (name_of_inv i) p m0.locks);
        assert (interp (fp `star` frame `star` locks_invariant opened_invariants m0) m0);
        assert (interp (fp `star` frame `star`
          (lock_store_invariant opened_invariants m0.locks `star`
          ctr_validity m0.ctr m0.ghost_ctr (heap_of_mem m0))) m0);

        move_invariant opened_invariants m0.locks p (name_of_inv i);
        assert (lock_store_invariant opened_invariants m0.locks `equiv`
                (p `star` lock_store_invariant (set_add (name_of_inv i) opened_invariants) m0.locks));

        with_inv_helper
          fp
          frame
          (lock_store_invariant opened_invariants m0.locks)
          (ctr_validity m0.ctr m0.ghost_ctr (heap_of_mem m0))
          p
          (lock_store_invariant (set_add (name_of_inv i) opened_invariants) m0.locks);

        assert (interp (p `star` fp `star` frame `star` locks_invariant (set_add (name_of_inv i) opened_invariants) m0) m0);
        MST.weaken <|
        MST.bind (f frame) (fun r ->
          MST.with_get (k1 r))
    in
    MST.weaken <|
    MST.bind (MST.recall _ (token_of_inv i)) (fun _ ->
    with_get_aux k0) 
 
let equiv_pqrs_p_qr_s (p q r s:slprop)
  : Lemma ((p `star` q `star` r `star` s) `equiv`
           (p `star` (q `star` r) `star` s))
  = star_associative p q r;
    slprop_extensionality
      (p `star` q `star` r)
      (p `star` (q `star` r))

let frame (#a:Type)
          (#opened_invariants:inames)
          (#pre:slprop)
          (#post:a -> slprop)
          (frame:slprop)
          ($f:action_except a opened_invariants pre post)
          (frame0:slprop)
  : _MstTot a opened_invariants (pre `star` frame) (fun x -> post x `star` frame) frame0
  = let aux
    : _mst_tot_aux a opened_invariants (pre `star` frame) (fun x -> post x `star` frame) frame0 (fun _ -> True)
    = fun m0 ->
        equiv_pqrs_p_qr_s pre frame frame0 (linv opened_invariants m0);
        assert (interp (pre `star` frame `star` frame0 `star` linv opened_invariants m0) m0);
        assert (interp (pre `star` (frame `star` frame0) `star` linv opened_invariants m0) m0);
        MST.weaken <| 
        MST.bind (f (frame `star` frame0)) (fun x ->
          let k
            : MST.mst_aux mem_evolves a 
              (fun m1 ->
                inames_ok opened_invariants m1 /\
                interp (post x `star` (frame `star` frame0) `star` linv opened_invariants m1) m1)
              (fun m0 x m1 -> 
                inames_ok opened_invariants m1 /\
                interp (post x `star` frame `star` frame0 `star` linv opened_invariants m1) m1)
            = fun m1 -> 
                equiv_pqrs_p_qr_s (post x) frame frame0 (linv opened_invariants m1);
                assert (interp (post x `star` (frame `star` frame0) `star` linv opened_invariants m1) m1);
                assert (interp (post x `star` frame `star` frame0 `star` linv opened_invariants m1) m1);
                MST.weaken <| MST.return x
          in
          MST.with_get k
        )
    in
    MST.weaken <| with_get_aux aux

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
    equiv_pqrs_p_qr_s pre frame frame0 (linv opened_invariants m0);
    assert (interp (pre `star` frame `star` frame0 `star` linv opened_invariants m0) m0);
    assert (interp (pre `star` (frame `star` frame0) `star` linv opened_invariants m0) m0);
    let x, m1 = f (frame `star` frame0) m0 in
    equiv_pqrs_p_qr_s (post x) frame frame0 (linv opened_invariants m1);
    assert (interp (post x `star` (frame `star` frame0) `star` linv opened_invariants m1) m1);
    assert (interp (post x `star` frame `star` frame0 `star` linv opened_invariants m1) m1);
    x, m1

let change_slprop (#opened_invariants:inames)
                  (p q:slprop)
                  (proof: (m:mem -> Lemma (requires interp p m) (ensures interp q m)))
: pst_ghost_action_except unit opened_invariants p (fun _ -> q)
= let proof (h:H.heap)
    : Lemma (requires H.interp p h)
            (ensures H.interp q h)
    = proof (mem_of_heap h)
  in
  lift_tot_action (lift_heap_action opened_invariants (H.change_slprop p q proof))

let witness_h_exists #opened_invariants #a p =
  lift_tot_action_with_frame (lift_heap_action_with_frame opened_invariants (H.elim_exists p))

let intro_exists #opened_invariants #a p x = 
  lift_tot_action_with_frame (lift_heap_action_with_frame opened_invariants (H.intro_exists p x))

let lift_h_exists #opened_invariants p = lift_tot_action (lift_heap_action opened_invariants (H.lift_exists p))

let elim_pure #opened_invariants p = lift_tot_action (lift_heap_action opened_invariants (H.elim_pure p))

let intro_pure #opened_invariants p pf = lift_tot_action (lift_heap_action opened_invariants (H.intro_pure p pf))

let drop #o p = lift_tot_action (lift_heap_action o (H.drop p))

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
      let m1 : full_mem = 
        { m0 with heap = H.upd_ghost_heap m0.heap (hide (m1'.heap));
                  ghost_ctr = (reveal m1').ghost_ctr } in
      let x = ni_a (hide (fst (reveal xm1))) in
      (x, m1)

(* Concrete small refs *)
let pts_to = H.pts_to

let sel_action #a #pcm e r v0
  = lift_tot_action (lift_heap_action e (H.sel_action #a #pcm r v0))

let upd_action #a #pcm e r v0 v1
  = lift_tot_action (lift_heap_action e (H.upd_action #a #pcm r v0 v1))

let free_action #a #pcm e r v0
  = lift_tot_action (lift_heap_action e (H.free_action #a #pcm r v0))

let split_action #a #pcm e r v0 v1
  = lift_tot_action (lift_heap_action e (H.split_action #a #pcm r v0 v1))

let gather_action #a #pcm e r v0 v1
  = lift_tot_action (lift_heap_action e (H.gather_action #a #pcm r v0 v1))

let weaken (p q r:slprop) (h:H.hheap (p `star` q) { H.stronger q r })
  : H.hheap (p `star` r)
  = H.weaken p q r h; h

let weaken_pure (q r: prop)
  : Lemma
    (requires (q ==> r))
    (ensures H.stronger (H.pure q) (H.pure r))
  = let aux (h:H.heap)
        : Lemma (ensures (H.interp (H.pure q) h ==> H.interp (H.pure r) h))
                [SMTPat ()]
        = H.pure_interp q h;
          H.pure_interp r h
    in
    ()

let inc_ctr (#p:slprop) #e (m:hmem_with_inv_except e p)
  : m':hmem_with_inv_except e p{m'.ctr = m.ctr + 1 /\ H.stronger (linv e m) (linv e m')}
  = let m' : mem = { m with ctr = m.ctr + 1} in
    assert (interp (p `star` linv e m) m');
    assert (linv e m == lock_store_invariant e m.locks
                        `star`
                        ctr_validity m.ctr m.ghost_ctr (heap_of_mem m));
    assert (linv e m' == lock_store_invariant e m.locks
                         `star`
                        ctr_validity (m.ctr + 1) m.ghost_ctr (heap_of_mem m));
    H.weaken_free_above CONCRETE (heap_of_mem m) m.ctr (m.ctr + 1);
    weaken_pure (heap_ctr_valid m.ctr m.ghost_ctr (heap_of_mem m))
                (heap_ctr_valid (m.ctr + 1) m.ghost_ctr (heap_of_mem m));
    assert (H.stronger
                  (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m))
                  (ctr_validity (m.ctr + 1) m.ghost_ctr (heap_of_mem m)));
    H.star_associative p (lock_store_invariant e m.locks)
                         (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m));
    H.stronger_star (lock_store_invariant e m.locks)
                    (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m))
                    (ctr_validity (m.ctr + 1) m.ghost_ctr (heap_of_mem m));
    H.weaken (p `star` lock_store_invariant e m.locks)
             (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m))
             (ctr_validity (m.ctr + 1) m.ghost_ctr (heap_of_mem m))
             (heap_of_mem m');
    H.star_associative p (lock_store_invariant e m.locks)
                         (ctr_validity (m.ctr + 1) m.ghost_ctr (heap_of_mem m));
    let m' : hmem_with_inv_except e p = m' in
    m'

let with_fresh_counter (#t:Type u#a) (#post:t -> slprop u#m) (e:inames)
  (f: (addr:nat ->
        H.action #MUTABLE #(Some CONCRETE)
          #(fun h -> h `H.free_above_addr CONCRETE` addr)
          #(fun h -> h `H.free_above_addr CONCRETE` (addr + 1))      
          emp 
          t
          post))
: pst_action_except t e emp post
= let f : refined_pre_action false e emp t post
    = fun m0 ->
        let h = hheap_of_hmem m0 in
        let (|r, h'|) = f m0.ctr h in
        let m' : hmem_with_inv_except e emp = inc_ctr m0 in
        let h' : H.hheap (post r `star` linv e m') = weaken _ (linv e m0) (linv e m') h' in
        let m1 : hmem_with_inv_except e (post r) = hmem_of_hheap m' h' in
        let aux (frame:slprop)
          : Lemma
            (requires
               interp ((emp `star` frame) `star` linv e m0) m0)
            (ensures
               interp ((post r `star` frame) `star` linv e m1) m1 /\
               mem_evolves m0 m1)
            [SMTPat (emp `star` frame)]
          = star_associative emp frame (linv e m0);
            assert (H.interp (emp `star` (frame `star` linv e m0)) h);
            assert (H.interp (post r `star` (frame `star` linv e m0)) h');
            star_associative (post r) frame (linv e m0);
            assert (H.interp ((post r `star` frame) `star` linv e m0) h');
            assert (H.stronger (linv e m0) (linv e m'));
            assert (H.equiv (linv e m') (linv e m1));
            assert (H.stronger (linv e m0) (linv e m1));
            let h' : H.hheap ((post r `star` frame) `star` linv e m1) = weaken _ (linv e m0) (linv e m1) h' in
            assert (H.interp ((post r `star` frame) `star` linv e m1) h')
        in
        assert (frame_related_mems emp (post r) e m0 m1);
        (| r, m1 |)
    in
    lift_tot_action (refined_pre_action_as_action f)


let alloc_action #a #pcm e x
  = with_fresh_counter e (H.extend #a #pcm x)

let select_refine #a #p e r x f
  = lift_tot_action (lift_heap_action e (H.select_refine #a #p r x f))

let upd_gen #a #p e r x y f
  = lift_tot_action (lift_heap_action e (H.upd_gen_action r x y f))

let pts_to_not_null_action
      (#a:Type u#a) (#pcm:pcm a)
      (e:inames)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r))) e
    (pts_to r v)
    (fun _ -> pts_to r v)
= lift_tot_action (lift_heap_action e (H.pts_to_not_null_action #a #pcm r v))

let ghost_ref = H.ghost_ref
let ghost_pts_to = H.ghost_pts_to


let inc_ghost_ctr (#p:slprop) #e (m:hmem_with_inv_except e p)
  : m':hmem_with_inv_except e p{reveal m'.ghost_ctr = m.ghost_ctr + 1 /\ H.stronger (linv e m) (linv e m')}
  = let m' : mem = { m with ghost_ctr = m.ghost_ctr + 1} in
    assert (interp (p `star` linv e m) m');
    assert (linv e m == lock_store_invariant e m.locks
                        `star`
                        ctr_validity m.ctr m.ghost_ctr (heap_of_mem m));
    assert (linv e m' == lock_store_invariant e m.locks
                         `star`
                        ctr_validity m.ctr (m.ghost_ctr + 1) (heap_of_mem m));
    H.weaken_free_above GHOST (heap_of_mem m) m.ghost_ctr (m.ghost_ctr + 1);
    weaken_pure (heap_ctr_valid m.ctr m.ghost_ctr (heap_of_mem m))
                (heap_ctr_valid m.ctr (m.ghost_ctr + 1) (heap_of_mem m));
    assert (H.stronger
                  (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m))
                  (ctr_validity m.ctr (m.ghost_ctr + 1) (heap_of_mem m)));
    H.star_associative p (lock_store_invariant e m.locks)
                         (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m));
    H.stronger_star (lock_store_invariant e m.locks)
                    (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m))
                    (ctr_validity m.ctr (m.ghost_ctr + 1) (heap_of_mem m));
    H.weaken (p `star` lock_store_invariant e m.locks)
             (ctr_validity m.ctr m.ghost_ctr (heap_of_mem m))
             (ctr_validity m.ctr (m.ghost_ctr + 1) (heap_of_mem m))
             (heap_of_mem m');
    H.star_associative p (lock_store_invariant e m.locks)
                         (ctr_validity m.ctr (m.ghost_ctr + 1) (heap_of_mem m));
    let m' : hmem_with_inv_except e p = m' in
    m'

let with_fresh_ghost_counter (#t:Type u#a) (#post:t -> slprop u#m) (e:inames)
  (f: (addr:erased nat ->
        H.action #ONLY_GHOST #(Some GHOST)
          #(fun h -> h `H.free_above_addr GHOST` addr)
          #(fun h -> h `H.free_above_addr GHOST` (addr + 1))      
          emp 
          t
          post))
: pst_ghost_action_except t e emp post
  = let f : refined_pre_action true e emp t post
    = fun m0 ->
        let h = hheap_of_hmem m0 in
        let (|r, h'|) = f m0.ghost_ctr h in
        let m' : hmem_with_inv_except e emp = inc_ghost_ctr m0 in
        let h' : H.hheap (post r `star` linv e m') = weaken _ (linv e m0) (linv e m') h' in
        let m1 : hmem_with_inv_except e (post r) = hmem_of_hheap m' h' in
        let aux (frame:slprop)
          : Lemma
            (requires
               interp ((emp `star` frame) `star` linv e m0) m0)
            (ensures
               interp ((post r `star` frame) `star` linv e m1) m1 /\
               mem_evolves m0 m1)
            [SMTPat (emp `star` frame)]
          = star_associative emp frame (linv e m0);
            assert (H.interp (emp `star` (frame `star` linv e m0)) h);
            assert (H.interp (post r `star` (frame `star` linv e m0)) h');
            star_associative (post r) frame (linv e m0);
            assert (H.interp ((post r `star` frame) `star` linv e m0) h');
            assert (H.stronger (linv e m0) (linv e m'));
            assert (H.equiv (linv e m') (linv e m1));
            assert (H.stronger (linv e m0) (linv e m1));
            let h' : H.hheap ((post r `star` frame) `star` linv e m1) = weaken _ (linv e m0) (linv e m1) h' in
            assert (H.interp ((post r `star` frame) `star` linv e m1) h')
        in
        assert (frame_related_mems emp (post r) e m0 m1);
        (| r, m1 |)
    in
    lift_tot_action (refined_pre_action_as_action f)

let ghost_alloc #e #a #pcm x
  = with_fresh_ghost_counter e (H.ghost_extend #a #pcm x)

let ghost_read #o #a #p r x f
  = lift_tot_action (lift_heap_action o (H.ghost_read #a #p r x f))
let ghost_write #o #a #p r x y f
  = lift_tot_action (lift_heap_action o (H.ghost_write #a #p r x y f)) 
let ghost_share #o #a #p r v0 v1
  = lift_tot_action (lift_heap_action o (H.ghost_share #a #p r v0 v1))
let ghost_gather #o #a #p r v0 v1
  = lift_tot_action (lift_heap_action o (H.ghost_gather #a #p r v0 v1))

let big_pts_to = H.big_pts_to

let big_sel_action #a #pcm e r v0
  = lift_tot_action (lift_heap_action e (H.big_sel_action #a #pcm r v0))

let big_upd_action #a #pcm e r v0 v1
  = lift_tot_action (lift_heap_action e (H.big_upd_action #a #pcm r v0 v1))

let big_free_action #a #pcm e r v0
  = lift_tot_action (lift_heap_action e (H.big_free_action #a #pcm r v0))

let big_split_action #a #pcm e r v0 v1
  = lift_tot_action (lift_heap_action e (H.big_split_action #a #pcm r v0 v1))

let big_gather_action #a #pcm e r v0 v1
  = lift_tot_action (lift_heap_action e (H.big_gather_action #a #pcm r v0 v1))


let big_alloc_action #a #pcm e x
  = with_fresh_counter e (H.big_extend #a #pcm x)

let big_select_refine #a #p e r x f
  = lift_tot_action (lift_heap_action e (H.big_select_refine #a #p r x f))

let big_upd_gen #a #p e r x y f
  = lift_tot_action (lift_heap_action e (H.big_upd_gen_action r x y f))

let big_pts_to_not_null_action
      (#a:Type u#(ua + 1)) (#pcm:pcm a)
      (e:inames)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r))) e
    (big_pts_to r v)
    (fun _ -> big_pts_to r v)
= lift_tot_action (lift_heap_action e (H.big_pts_to_not_null_action #a #pcm r v))


let big_ghost_pts_to = H.big_ghost_pts_to
let big_ghost_alloc #e #a #pcm x
  = with_fresh_ghost_counter e (H.big_ghost_extend #a #pcm x)
let big_ghost_read #o #a #p r x f
  = lift_tot_action (lift_heap_action o (H.big_ghost_read #a #p r x f))
let big_ghost_write #o #a #p r x y f
  = lift_tot_action (lift_heap_action o (H.big_ghost_write #a #p r x y f)) 
let big_ghost_share #o #a #p r v0 v1
  = lift_tot_action (lift_heap_action o (H.big_ghost_share #a #p r v0 v1))
let big_ghost_gather #o #a #p r v0 v1
  = lift_tot_action (lift_heap_action o (H.big_ghost_gather #a #p r v0 v1))

