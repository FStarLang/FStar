(*
   Copyright 2024 Microsoft Research

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

module PulseCore.IndirectionTheorySep
module F = FStar.FunctionalExtensionality
module PM = PulseCore.MemoryAlt
module B = PulseCore.BaseHeapSig
open Pulse.Lib.Loc
open FStar.Ghost 

let timeless_mem : Type u#4 = PM.mem u#0

val mem: Type u#4
val timeless_mem_of: mem -> timeless_mem
val level (k:mem) : GTot nat
val credits (k:mem) : GTot nat
val current_loc (k:mem) : loc_id
let budget (m: mem) : GTot int = level m - credits m - 1
val update_timeless_mem (m: mem) (p: timeless_mem) :
  n:mem { timeless_mem_of n == p /\ level m == level n /\ credits m == credits n /\ current_loc m == current_loc n }
val update_loc (m:mem) (l:loc_id) :
  n:mem { timeless_mem_of n == timeless_mem_of m /\ level m == level n /\ credits m == credits n /\ current_loc n == l }

[@@erasable] val slprop : Type u#4

val age1 (k:mem) : mem


val is_ghost_action : p:(mem -> mem -> prop) { FStar.Preorder.preorder_rel p }

val lift_ghost_action (m: mem) (p: timeless_mem) :
  Lemma (PM.is_ghost_action (timeless_mem_of m) p <==> is_ghost_action m (update_timeless_mem m p))
    [SMTPat (is_ghost_action m (update_timeless_mem m p))]

val update_ghost :
      m0:mem ->
      m1:FStar.Ghost.erased mem { is_ghost_action m0 m1 } ->
      m:mem { m == FStar.Ghost.reveal m1 }

let is_full (m:mem) 
: prop
= PM.full_mem_pred u#0 (timeless_mem_of m)
let full_mem = m:mem { is_full m  }

val emp : slprop
val pure (p:prop) : slprop
val star (p q:slprop) : slprop
val ( exists* ) (#a:Type u#a) (f:a -> slprop) : slprop
val exists_ext (#a:Type u#a) (p q : a -> slprop)
: Lemma
  (requires F.feq p q)
  (ensures op_exists_Star p == op_exists_Star q)

val sep_laws (_:unit) : squash (
  PulseCore.Semantics.(
    associative star /\
    commutative star /\
    is_unit emp star
  )
)

val disjoint (m0 m1:mem) : p:prop { p ==>
    B.disjoint_mem (timeless_mem_of m0) (timeless_mem_of m1) /\
    current_loc m0 == current_loc m1 /\
    level m0 == level m1 }
val join (m0:mem) (m1:mem { disjoint m0 m1 }) :
  n:mem { timeless_mem_of n == B.join_mem (timeless_mem_of m0) (timeless_mem_of m1) }
val clear_except_hogs (i:mem) : mem
val join_refl (i:mem)
: Lemma (disjoint i (clear_except_hogs i) /\ join i (clear_except_hogs i) == i)

val disjoint_join_levels (i0 i1:mem)
: Lemma 
  (requires
    disjoint i0 i1)
  (ensures
    level i0 == level i1 /\
    level (join i0 i1) == level i0 /\
    credits (join i0 i1) == credits i0 + credits i1)

let join_mem (m0:mem) (m1:mem { disjoint m0 m1 }) : m:mem { m == join m0 m1 } = join m0 m1

let affine_prop (p: mem -> prop) =
  forall (m0 m1:mem). p m0 /\ disjoint m0 m1 ==> p (join m0 m1)

val interp (p:slprop) : q:(mem  -> prop) { affine_prop q }

val update_timeless_mem_id (m: mem) :
  Lemma (update_timeless_mem m (timeless_mem_of m) == m)
    [SMTPat (update_timeless_mem m (timeless_mem_of m))]

val join_update_timeless_mem (m1 m2: mem) (p1 p2: timeless_mem) :
  Lemma (requires disjoint m1 m2 /\ B.disjoint_mem p1 p2)
    (ensures disjoint (update_timeless_mem m1 p1) (update_timeless_mem m2 p2) /\
      join_mem (update_timeless_mem m1 p1) (update_timeless_mem m2 p2) ==
        update_timeless_mem (join_mem m1 m2) (B.join_mem p1 p2))

val star_equiv :
      p:slprop ->
      q:slprop ->
      m:mem ->
      Lemma (
        interp (p `star` q) m <==> 
      (exists m0 m1. 
          disjoint m0 m1 /\
          m == join m0 m1 /\
          interp p m0 /\
          interp q m1))

val split_mem (p:slprop) (q:slprop) (m:erased mem { interp (p `star` q) m })
: res:(erased mem & erased mem) {
    let l, r = res in
    disjoint l r /\
    reveal m == join l r /\
    level l == level m /\ level r == level m /\
    current_loc l == current_loc m /\ current_loc r == current_loc m /\
    interp p l /\
    interp q r
}

val intro_star (p q:slprop) (m0 m1:mem)
: Lemma
  (requires disjoint m0 m1 /\ interp p m0 /\ interp q m1)
  (ensures interp (p `star` q) (join m0 m1))

val emp_equiv (m:mem) : Lemma (interp emp m)

val interp_exists (#a:Type u#a) (p: a -> slprop)
: Lemma (forall m. interp (op_exists_Star p) m <==> (exists x. interp (p x) m))

val interp_pure (p:prop) (m:mem)
: Lemma (interp (pure p) m <==> p)

let destruct_star_l (p q:slprop) (m:mem)
: Lemma (interp (p `star` q) m ==> interp p m)
= introduce interp (p `star` q) m ==> interp p m
  with _ . (
    star_equiv p q m;
    eliminate exists c0 c1.
        disjoint c0 c1 /\
        m == join c0 c1 /\
        interp p c0 /\
        interp q c1
    returns interp p m
    with _ . (
        star_equiv p emp m;
        emp_equiv c1
    )
 )


let destruct_star (p q:slprop) (m:mem)
: Lemma
  (requires interp (p `star` q) m)
  (ensures interp p m /\ interp q m)
= sep_laws ();
  destruct_star_l p q m;
  destruct_star_l q p m

let pm_slprop : Type u#4 = PM.slprop u#0
val lift (p:pm_slprop) : slprop

val lift_eq (p:PM.slprop)
: Lemma (forall m. interp (lift p) m ==
                   B.interp p (timeless_mem_of m))

val lift_emp_eq () : Lemma (
  lift PM.emp == emp
)
val lift_pure_eq (p:prop) : Lemma (
  lift (PM.pure p) == pure p
)
val lift_star_eq (p q:pm_slprop) : Lemma (
  lift (PM.star p q) == star (lift p) (lift q)
)

val later (p:slprop) : slprop
val later_credit (n:nat) : slprop

val later_credit_zero () : squash (later_credit 0 == emp)
val later_credit_add m n : squash (later_credit (m + n) == later_credit m `star` later_credit n)

val implies (p q: slprop) : prop
val elim_implies p q (m: mem { level m > 0 }) :
  squash (implies p q /\ interp p m ==> interp q m)
let elim_implies' #p #q (h: squash (implies p q)) (m: mem { level m > 0 }) :
    squash (interp p m ==> interp q m) =
  elim_implies p q m

let timeless (p: slprop) : prop = later p `implies` p
val timeless_lift p : squash (timeless (lift p))
val timeless_pure p : squash (timeless (pure p))
val timeless_emp () : squash (timeless emp)
val timeless_later_credit n : squash (timeless (later_credit n))
val later_star p q : squash (later (star p q) == star (later p) (later q))
val timeless_star p q : Lemma (requires timeless p /\ timeless q) (ensures timeless (star p q))
val later_exists #t (f:t->slprop) :
  squash (later (exists* x. f x) `implies` (exists* x. later (f x))
      /\ (exists* x. later (f x)) `implies` later (exists* x. f x))
val timeless_exists (#t: Type) (f: t->slprop) : Lemma (requires forall x. timeless (f x)) (ensures timeless (exists* x. f x))

val equiv (p q:slprop) : slprop
val intro_equiv (p: slprop) m : squash (interp (equiv p p) m)
val equiv_comm (p q: slprop) : squash (equiv p q == equiv q p)
val equiv_elim p q : squash (equiv p q `star` p == equiv p q `star` q)
val equiv_trans (p q r: slprop) : squash (equiv p q `star` equiv q r == equiv p q `star` equiv p r)
val later_equiv (p q: slprop) : squash (later (equiv p q) == equiv (later p) (later q))
val equiv_timeless (a b: slprop) : Lemma (requires timeless a /\ timeless b) (ensures equiv a b == pure (a == b))
val equiv_star_congr (p q r: slprop) : squash (equiv q r == equiv q r `star` equiv (star p q) (star p r))

val intro_later (p:slprop) (m:mem)
: Lemma (interp p m ==> interp (later p) m)

val set_loc (m: mem) (l: loc_id) : (m':mem {
  budget m' == budget m /\
  (is_full m' <==> is_full m) /\
  current_loc m' == l /\
  is_ghost_action m m' /\
  timeless_mem_of m' == timeless_mem_of m
})

val set_loc_set_loc' m l1 l2 : squash (set_loc (set_loc m l1) l2 == set_loc m l2)
val set_loc_current_loc' m : squash (set_loc m (current_loc m) == m)

val join_set_loc a b l : Lemma (requires disjoint a b)
  (ensures disjoint (set_loc a l) (set_loc b l) /\ join (set_loc a l) (set_loc b l) == set_loc (join a b) l)

val loc (l:loc_id) : (p:slprop { timeless p })
val interp_loc l m : squash (interp (loc l) m <==> l == current_loc m)
val loc_dup_eq l : squash (star (loc l) (loc l) == loc l)
val loc_gather_eq l1 l2 : squash (star (loc l1) (loc l2) == star (loc l1) (pure (l1 == l2)))

val on (l:loc_id) (p:slprop) : slprop
val interp_on l p m : squash (interp (on l p) m <==> interp p (set_loc m l))
val loc_on_eq l p : squash (star (loc l) p == star (loc l) (on l p))
val timeless_on l (p: slprop { timeless p }) : squash (timeless (on l p))
val on_emp l : squash (on l emp == emp)
val on_star_eq l a b : squash (on l (star a b) == star (on l a) (on l b))
val on_on_eq l1 l2 a : squash (on l1 (on l2 a) == on l2 a)
val on_loc_eq l1 l2 : squash (on l1 (loc l2) == pure (l1 == l2))
val on_loc_same_eq l : squash (on l (loc l) == emp)
val on_later_credit_eq l n : squash (on l (later_credit n) == later_credit n)
val on_later_eq l p : squash (on l (later p) == later (on l p))
val on_equiv_eq l a b : squash (on l (equiv a b) == equiv a b)
val on_lift_eq l p : squash (on l (lift p) == lift p)

(**** Memory invariants *)
[@@erasable]
val iref : Type0

val inv (i:iref) (p:slprop) : slprop

val deq_iref : FStar.GhostSet.decide_eq iref
let inames = FStar.GhostSet.set iref

(** This proposition tells us that all the invariants names in [e] are valid in memory [m] *)
val hogs_inames_ok (e:inames) (m:mem) : prop
let inames_ok (e:inames) (m:mem) : prop
= hogs_inames_ok e m

val inames_ok_set_loc ictx m l : squash (inames_ok ictx (set_loc m l) <==> inames_ok ictx m)

(** The empty set of invariants is always empty *)
val inames_ok_empty (m:mem)
  : Lemma (ensures inames_ok GhostSet.empty m)
val inames_ok_union (i j:inames) (m:mem)
: Lemma 
  (inames_ok (FStar.GhostSet.union i j) m <==>
   inames_ok i m /\
   inames_ok j m)

let somewhere (p: slprop) = exists* l. on l p

val iname_ok (i: iref) (m: mem) : prop
val read_inv (i: iref) (m: mem { iname_ok i m }) : slprop

val hogs_invariant (ex:inames) (i:mem) : slprop

let mem_invariant (e:inames) (w:mem) : slprop
= hogs_invariant e w

val inames_ok_update_timeless_mem (m: mem) (p: timeless_mem) (ex: inames) :
  Lemma (inames_ok ex (update_timeless_mem m p) <==> inames_ok ex m)
    [SMTPat (inames_ok ex (update_timeless_mem m p))]

val hogs_invariant_update_timeless_mem (m: mem) (p: timeless_mem) (ex: inames) :
  Lemma (hogs_invariant ex (update_timeless_mem m p) == hogs_invariant ex m)
    [SMTPat (hogs_invariant ex (update_timeless_mem m p))]

val hogs_dom (m:mem) : inames

val age_mem (m:mem) : m':mem { 
  m' == age1 m /\
  is_ghost_action m m' /\
  timeless_mem_of m' == timeless_mem_of m /\
  (hogs_dom m == hogs_dom m')
}
val age_level (m:mem)
: Lemma
  (requires level m > 0)
  (ensures level (age1 m) == level m - 1 /\
            credits (age1 m) == credits m)
val age_disjoint (m0 m1:mem)
: Lemma
  (requires disjoint m0 m1)
  (ensures 
    disjoint (age1 m0) (age1 m1) /\
    age1 (join m0 m1) == join (age1 m0) (age1 m1))
val age_hereditary (p:slprop) (m:mem)
: Lemma (interp p m ==> interp p (age1 m))
val age_later (p:slprop) (m:mem)
: Lemma
  (interp (later p) m <==> (level m > 0 ==> interp p (age1 m)))

val spend_mem (m:mem) : m':mem { 
  is_ghost_action m m' /\
  timeless_mem_of m' == timeless_mem_of m /\
  (hogs_dom m == hogs_dom m')
}
let spend (m:mem) : mem = spend_mem m
val interp_later_credit (n:nat) (m:mem)
: Lemma (interp (later_credit n) m <==> credits m >= n)
val spend_lemma (m:mem)
: Lemma 
  (requires
    credits m > 0)
  (ensures (
    let m' = spend m in
    level m' == level m /\
    credits m' == credits m - 1))
val spend_disjoint (m0 m1:mem)
: Lemma
  (requires
    disjoint m0 m1 /\
    credits m0 > 0)
  (ensures
    disjoint (spend m0) m1 /\
    spend (join m0 m1) == join (spend m0) m1)

let single (i:iref) : inames = FStar.GhostSet.singleton deq_iref i
let add_inv (e:inames) (i:iref)
: inames
= FStar.GhostSet.(union (single i) e)

let mem_inv (e:inames) (i:iref)
: GTot bool
= GhostSet.mem i e

val inames_ok_single (i: iref) (p:slprop) (m:mem)
: Lemma
  (requires interp (inv i p) m)
  (ensures iname_ok i m)

val iname_ok_inames_ok (i:iref) (m:mem)
: Lemma (inames_ok (single i) m <==> iname_ok i m)
        [SMTPat (inames_ok (single i) m)]

val read_inv_intro (i:iref) (m:mem) p :
  Lemma (requires interp (later p `star` inv i p) m)
    (ensures iname_ok i m /\ interp (read_inv i m) m)

val read_inv_intro' (i:iref) (m:mem) p :
  Lemma (requires interp (somewhere (later p) `star` inv i p) m)
    (ensures iname_ok i m /\ interp (read_inv i m) m)

val read_inv_elim (i:iref) (m:mem { iname_ok i m }) p :
  Lemma
    (requires interp (read_inv i m `star` inv i p) m)
    (ensures interp (somewhere (later p)) m)

val read_inv_disjoint (i:iref) (m0 m1:mem)
: Lemma 
  (requires
    disjoint m0 m1 /\
    iname_ok i m0)
  (ensures 
    iname_ok i (join m0 m1) /\
    read_inv i m0 == read_inv i (join m0 m1))

val mem_invariant_equiv :
      e:inames ->
      m:mem ->
      i:iref { iname_ok i m } ->
      Lemma
        (requires
          ~(mem_inv e i))
        (ensures
          (mem_invariant e m ==
           mem_invariant (add_inv e i) m `star` read_inv i m))

val on_mem_invariant l ictx m : squash (on l (mem_invariant ictx m) == mem_invariant ictx m)

val mem_invariant_set_loc ictx m l : squash (mem_invariant ictx (set_loc m l) == mem_invariant ictx m)

val inames_ok_hogs_dom (e:inames) (m:mem)
: Lemma (inames_ok e m ==> FStar.GhostSet.subset e (hogs_dom m))

val inames_ok_update (e:inames) (m0 m1:mem)
: Lemma 
  (requires hogs_dom m0 == hogs_dom m1)
  (ensures inames_ok e m0 <==> inames_ok e m1)

val inames_ok_disjoint (i j:inames) (mi mj:mem)
: Lemma
  (requires
    disjoint mi mj /\
    inames_ok i mi /\
    inames_ok j mj)
  (ensures
    inames_ok (FStar.GhostSet.union i j) (join_mem mi mj))

val mem_invariant_disjoint (e f:inames) (p0 p1:slprop) (m0 m1:mem)
: Lemma
  (requires
    disjoint m0 m1 /\
    FStar.GhostSet.disjoint (hogs_dom m0) (hogs_dom m1) /\
    timeless_mem_of m1 == B.empty_mem /\
    interp (p0 `star` mem_invariant e m0) m0 /\
    interp (p1 `star` mem_invariant f m1) m1)
  (ensures (
    let m = join_mem m0 m1 in
    interp (p0 `star` p1 `star` mem_invariant (FStar.GhostSet.union e f) m) m))

val mem_invariant_age (e:inames) (m0:mem) (m1:mem { 1 < level m1 /\ level m1 <= level m0 })
: Lemma
  (ensures 
    interp (mem_invariant e m0) m1 ==>
    interp (mem_invariant e (age_mem m0)) (age1 m1))

val mem_invariant_spend (e:inames) (m:mem)
: Lemma
  (ensures mem_invariant e m == mem_invariant e (spend_mem m))

val buy1_mem (m: mem { budget m > 0 }) : m': mem {
  credits m' == 1 /\
  disjoint m' m /\
  (forall e. mem_invariant e m == mem_invariant e (join_mem m' m)) /\
  (forall e. inames_ok e m <==> inames_ok e (join_mem m' m)) /\
  (is_full m ==> is_full (join_mem m' m)) /\
  is_ghost_action m (join_mem m' m)
}

val inames_live (e:inames) : slprop
val inames_live_empty () : squash (emp == inames_live GhostSet.empty)
val inames_live_union (i j:inames) : squash (inames_live (GhostSet.union i j) == inames_live i `star` inames_live j)
val inames_live_inv (i:iref) (p:slprop) (m:mem) : squash (interp (inv i p) m ==> interp (inames_live (single i)) m)

val fresh_inv
    (p:slprop)
    (m:mem)
    (ctx:inames { Pulse.Lib.GhostSet.is_finite ctx })
: i:iref &
  m':mem { 
    not (GhostSet.mem i ctx) /\
    disjoint m m' /\
    is_ghost_action m (join_mem m m') /\
    timeless_mem_of (join_mem m m') == timeless_mem_of m /\
    inames_ok (single i) m' /\
    interp (inv i p `star` mem_invariant (single i) m') m' /\
    FStar.GhostSet.disjoint (hogs_dom m) (hogs_dom m') /\
    timeless_mem_of m' == B.empty_mem /\
    credits m' == 0
  }

val dup_inv_equiv :
    i:iref ->
    p:slprop ->
    Lemma (inv i p == (inv i p `star` inv i p))

val invariant_name_identifies_invariant (i: iref) (p q: slprop) :
  squash (star (inv i p) (inv i q) `implies` later (equiv p q))

val on_inv_eq l i p : squash (on l (inv i p) == inv i p)

(**** References to predicates *)
[@@erasable]
val slprop_ref : Type0

val null_slprop_ref : slprop_ref

val slprop_ref_pts_to (x: slprop_ref) (y: slprop) : slprop

val fresh_slprop_ref
    (p:slprop)
    (m:mem)
: i:slprop_ref &
  m':mem { 
    disjoint m m' /\
    is_ghost_action m (join_mem m m') /\
    timeless_mem_of (join_mem m m') == timeless_mem_of m /\
    interp (slprop_ref_pts_to i p `star` mem_invariant GhostSet.empty m') m' /\
    hogs_dom m' == GhostSet.empty /\
    timeless_mem_of m' == B.empty_mem /\
    credits m' == 0
  }

val slprop_ref_pts_to_share (x: slprop_ref) (y: slprop)
: Lemma (slprop_ref_pts_to x y == slprop_ref_pts_to x y `star` slprop_ref_pts_to x y)

val slprop_ref_pts_to_gather (x: slprop_ref) (y1 y2: slprop) 
: squash ((slprop_ref_pts_to x y1 `star` slprop_ref_pts_to x y2) `implies`
          (slprop_ref_pts_to x y1 `star` later (equiv y1 y2)))

val on_slprop_ref_pts_to_eq l x y : squash (on l (slprop_ref_pts_to x y) == slprop_ref_pts_to x y)