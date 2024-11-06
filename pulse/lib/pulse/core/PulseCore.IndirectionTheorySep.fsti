module PulseCore.IndirectionTheorySep
module F = FStar.FunctionalExtensionality
module T = FStar.Tactics
module PM = PulseCore.MemoryAlt
open FStar.Ghost 

let pulse_mem : Type u#4 = PM.mem u#0
val mem: Type u#4
val pulse_mem_of: mem -> pulse_mem

val age1 (k:mem) : mem


[@@erasable]
val slprop : Type u#4
val level (k:mem) : GTot nat
val credits (k:mem) : GTot nat

val update_pulse_mem (m: mem) (p: pulse_mem) :
  n:mem { pulse_mem_of n == p /\ level m == level n /\ credits m == credits n }

let level_at_least_credits (m:mem)
: GTot bool
= level m > credits m

val is_ghost_action : p:(mem -> mem -> prop) { FStar.Preorder.preorder_rel p }

val lift_ghost_action (m: mem) (p: pulse_mem) :
  Lemma (PM.is_ghost_action (pulse_mem_of m) p <==> is_ghost_action m (update_pulse_mem m p))
    [SMTPat (is_ghost_action m (update_pulse_mem m p))]

val update_ghost :
      m0:mem ->
      m1:FStar.Ghost.erased mem { is_ghost_action m0 m1 } ->
      m:mem { m == FStar.Ghost.reveal m1 }

let is_full (m:mem) : prop = PM.pulse_heap_sig.full_mem_pred (pulse_mem_of m)
let full_mem = m:mem { is_full m }

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
    PM.pulse_heap_sig.sep.disjoint (pulse_mem_of m0) (pulse_mem_of m1) /\
    level m0 == level m1 }
val join (m0:mem) (m1:mem { disjoint m0 m1 }) :
  n:mem { pulse_mem_of n == PM.pulse_heap_sig.sep.join (pulse_mem_of m0) (pulse_mem_of m1) }
val clear_except_istore (i:mem) : mem
val join_refl (i:mem)
: Lemma (disjoint i (clear_except_istore i) /\ join i (clear_except_istore i) == i)

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

val update_pulse_mem_id (m: mem) :
  Lemma (update_pulse_mem m (pulse_mem_of m) == m)
    [SMTPat (update_pulse_mem m (pulse_mem_of m))]

val join_update_pulse_mem (m1 m2: mem) (p1 p2: pulse_mem) :
  Lemma (requires disjoint m1 m2 /\ PM.pulse_heap_sig.sep.disjoint p1 p2)
    (ensures disjoint (update_pulse_mem m1 p1) (update_pulse_mem m2 p2) /\
      join_mem (update_pulse_mem m1 p1) (update_pulse_mem m2 p2) ==
        update_pulse_mem (join_mem m1 m2) (PM.pulse_heap_sig.sep.join p1 p2))

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
                   PM.pulse_heap_sig.interp p (pulse_mem_of m))

val lift_emp_eq () : Lemma (
  lift PM.emp == emp
)
val lift_pure_eq (p:prop) : Lemma (
  lift (PM.pure p) == pure p
)
val lift_star_eq (p q:pm_slprop) : Lemma (
  lift (PM.star p q) == star (lift p) (lift q)
)
// val lift_exists_eq (a:Type u#4) (f:a -> pm_slprop) : Lemma (
//   lift PM.(h_exists #a f) == (exists* (x:a). lift (f x))
// )

(**** Memory invariants *)
[@@erasable]
val iref : Type0
val deq_iref : FStar.GhostSet.decide_eq iref
let inames = FStar.GhostSet.set iref
val lower_inames (i:inames) : PM.inames

(** This proposition tells us that all the invariants names in [e] are valid in memory [m] *)
val istore_inames_ok (e:inames) (m:mem) : prop
let inames_ok (e:inames) (m:mem) : prop
= HeapSig.inames_ok #PM.pulse_heap_sig (lower_inames e) (pulse_mem_of m) /\
  istore_inames_ok e m

(** The empty set of invariants is always empty *)
val inames_ok_empty (m:mem)
  : Lemma (ensures inames_ok GhostSet.empty m)
val inames_ok_union (i j:inames) (m:mem)
: Lemma 
  (inames_ok (FStar.GhostSet.union i j) m <==>
   inames_ok i m /\
   inames_ok j m)

val istore_invariant (ex:inames) (i:mem) : slprop

let mem_invariant (e:inames) (w:mem) : slprop
=  lift (PM.mem_invariant (lower_inames e) (pulse_mem_of w)) `star`
   istore_invariant e w

val inames_ok_update_pulse_mem (m: mem) (p: pulse_mem) (ex: inames) :
  Lemma (inames_ok ex (update_pulse_mem m p) <==> inames_ok ex m)
    [SMTPat (inames_ok ex (update_pulse_mem m p))]

val istore_invariant_update_pulse_mem (m: mem) (p: pulse_mem) (ex: inames) :
  Lemma (istore_invariant ex (update_pulse_mem m p) == istore_invariant ex m)
    [SMTPat (istore_invariant ex (update_pulse_mem m p))]

val inv (i:iref) (p:slprop) : slprop

val later (p:slprop) : slprop
val later_credit (n:nat) : slprop

val later_credit_zero () : squash (later_credit 0 == emp)
val later_credit_add m n : squash (later_credit (m + n) == later_credit m `star` later_credit n)

let timeless (p: slprop) = later p == p
val timeless_lift p : squash (timeless (lift p))
val timeless_pure p : squash (timeless (pure p))
val timeless_emp () : squash (timeless emp)
val timeless_later_credit n : squash (timeless (later_credit n))
val later_star p q : squash (later (star p q) == star (later p) (later q))
val later_exists #t (f:t->slprop) : squash (later (exists* x. f x) == (exists* x. later (f x)))

val equiv (p q:slprop) : slprop
val intro_equiv (p: slprop) m : squash (interp (equiv p p) m)
val equiv_comm (p q: slprop) : squash (equiv p q == equiv q p)
val equiv_elim p q : squash (equiv p q `star` p == equiv p q `star` q)
val equiv_trans (p q r: slprop) : squash (equiv p q `star` equiv q r == equiv p q `star` equiv p r)
val equiv_timeless (a b: slprop) : Lemma (requires timeless a /\ timeless b) (ensures equiv a b == pure (a == b))
val equiv_star_congr (p q r: slprop) : squash (equiv q r == equiv q r `star` equiv (star p q) (star p r))

val intro_later (p:slprop) (m:mem)
: Lemma (interp p m ==> interp (later p) m)
val istore_dom (m:mem) : inames

val age_mem (m:mem) : m':mem { 
  m' == age1 m /\
  is_ghost_action m m' /\
  pulse_mem_of m' == pulse_mem_of m /\
  (istore_dom m == istore_dom m')
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
  (requires level m > 0)
  (ensures interp (later p) m ==> interp p (age1 m))

val spend_mem (m:mem) : m':mem { 
  is_ghost_action m m' /\
  pulse_mem_of m' == pulse_mem_of m /\
  (istore_dom m == istore_dom m')
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

val buy_mem (n:FStar.Ghost.erased nat) (m:mem) : m':mem {
  is_ghost_action m m' /\
  pulse_mem_of m' == pulse_mem_of m /\
  (istore_dom m == istore_dom m')
}
let buy (n:nat) (m:mem) : mem = buy_mem n m
val buy_lemma (n:nat) (m:mem)
: Lemma (
  let m' = buy n m in
  level m' == level m /\
  credits m' == credits m + n
)
val buy_disjoint (n:nat) (m0 m1:mem)
: Lemma
  (requires
    disjoint m0 m1)
  (ensures
    disjoint (buy n m0) m1 /\
    buy n (join m0 m1) == join (buy n m0) m1)

let single (i:iref) : inames = FStar.GhostSet.singleton deq_iref i
let add_inv (e:inames) (i:iref)
: inames
= FStar.GhostSet.(union (single i) e)

let mem_inv (e:inames) (i:iref)
: GTot bool
= GhostSet.mem i e

val iname_ok (i: iref) (m: mem) : prop
val inames_ok_single (i: iref) (p:slprop) (m:mem)
: Lemma
  (requires interp (inv i p) m)
  (ensures iname_ok i m)

val iname_ok_inames_ok (i:iref) (m:mem)
: Lemma (inames_ok (single i) m <==> iname_ok i m)
        [SMTPat (inames_ok (single i) m)]

val read_inv (i: iref) (m: mem { iname_ok i m }) : slprop
val read_inv_equiv (i:iref) (m:mem { iname_ok i m /\ level m > 0 }) p 
: Lemma
  (requires 
    interp (inv i p) m)
  (ensures
    interp (later (read_inv i m)) m
    <==>
    interp (later p) m)

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
           mem_invariant (add_inv e i) m `star` later (read_inv i m)))


val inames_ok_istore_dom (e:inames) (m:mem)
: Lemma (inames_ok e m ==> FStar.GhostSet.subset e (istore_dom m))

val inames_ok_update (e:inames) (m0 m1:mem)
: Lemma 
  (requires istore_dom m0 == istore_dom m1)
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
    FStar.GhostSet.disjoint (istore_dom m0) (istore_dom m1) /\
    pulse_mem_of m1 == PM.pulse_heap_sig.sep.empty /\
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

val mem_invariant_buy (e:inames) (n:nat) (m:mem)
: Lemma
  (ensures mem_invariant e m == mem_invariant e (buy_mem n m))

let fresh_wrt (ctx:list iref)
              (i:iref)
  = forall i'. List.Tot.memP i' ctx ==> i' =!= i

val fresh_inv
    (p:slprop)
    (m:mem)
    (ctx:FStar.Ghost.erased (list iref))
: i:iref &
  m':mem { 
    fresh_wrt ctx i /\
    disjoint m m' /\
    is_ghost_action m (join_mem m m') /\
    pulse_mem_of (join_mem m m') == pulse_mem_of m /\
    inames_ok (single i) m' /\
    interp (inv i p `star` mem_invariant (single i) m') m' /\
    FStar.GhostSet.disjoint (istore_dom m) (istore_dom m') /\
    pulse_mem_of m' == PM.pulse_heap_sig.sep.empty /\
    credits m' == 0
  }

val dup_inv_equiv :
    i:iref ->
    p:slprop ->
    Lemma (inv i p == (inv i p `star` inv i p))

val invariant_name_identifies_invariant (i: iref) (p q: slprop) (m: mem { level m > 0 }) :
  Lemma (interp (star (inv i p) (inv i q)) m ==> interp (later (equiv p q)) m)