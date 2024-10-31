module PulseCore.IndirectionTheorySep
module F = FStar.FunctionalExtensionality
module T = FStar.Tactics
module PM = PulseCore.MemoryAlt

[@@erasable] val istore : Type u#4
[@@erasable] val core_istore : Type u#4
let pulse_mem : Type u#4 = PM.mem u#0
let pulse_core_mem : Type u#4 = PM.pulse_heap_sig.sep.core
noeq type mem = { istore:istore; pulse_mem:PM.mem u#0 }
noeq type core_mem = { istore:core_istore; pulse_mem:pulse_core_mem }
val istore_core (i:istore) : core_istore
let core_of (m:mem)
: core_mem
= { istore = istore_core m.istore; pulse_mem = PM.pulse_heap_sig.sep.core_of m.pulse_mem }

val age1 (k:core_mem) : core_mem


[@@erasable]
val slprop : Type u#4
val ilevel (_:core_istore) : GTot nat
val level (k:core_mem) : GTot nat
val level_depends_on_core_istore_only (m:core_mem) 
: Lemma (level m == ilevel m.istore)
        [SMTPat (level m)]

val icredits (_:core_istore) : GTot nat
let credits (k:core_mem) : GTot nat = icredits k.istore
let level_at_least_credits (m:mem)
: GTot bool
= level (core_of m) >= credits (core_of m)

let level_decreases_by_spent_credits (m0 m1:mem)
: prop
= let l0, c0 = level (core_of m0), credits (core_of m0) in
  let l1, c1 = level (core_of m1), credits (core_of m1) in
  c1 <= c0 /\ //credits decrease
  l1 == l0 - (c0 - c1) // and level decreases by the amount of credits spent
let has_credits (m:mem) : GTot bool = credits (core_of m) > 0

val is_ghost_action_istore : p:(istore -> istore -> prop) { 
    FStar.Preorder.preorder_rel p 
}

let is_ghost_action (m0 m1:mem) : prop = 
  is_ghost_action_istore m0.istore m1.istore /\
  PM.is_ghost_action m0.pulse_mem m1.pulse_mem

val update_ghost :
      m0:mem ->
      m1:FStar.Ghost.erased mem { is_ghost_action m0 m1 } ->
      m:mem { m == FStar.Ghost.reveal m1 }
    
let is_full (m:mem) : prop = PM.pulse_heap_sig.full_mem_pred m.pulse_mem
let full_mem = m:mem { is_full m }

val emp : slprop
val pure (p:prop) : slprop
val star (p q:slprop) : slprop

val ( exists* ) (#a:Type u#a) (f:a -> slprop) : slprop

val sep_laws (_:unit) : squash (
  PulseCore.Semantics.(
    associative star /\
    commutative star /\
    is_unit emp star
  )
)


val istore_disjoint (i0 i1:core_istore) : prop
val istore_join (i0:core_istore) (i1:core_istore { istore_disjoint i0 i1}) : core_istore
val clear_credits (i:core_istore) : core_istore
val istore_join_refl (i:core_istore)
: Lemma (istore_disjoint i (clear_credits i) /\ istore_join i (clear_credits i) == i)
let disjoint (m0 m1:core_mem)
: prop
= PM.pulse_heap_sig.sep.disjoint m0.pulse_mem m1.pulse_mem /\
  istore_disjoint m0.istore m1.istore
let join (m0:core_mem) (m1:core_mem { disjoint m0 m1 })
: core_mem
= { pulse_mem = PM.pulse_heap_sig.sep.join m0.pulse_mem m1.pulse_mem;
    istore = istore_join m0.istore m1.istore }

val disjoint_join_levels (i0 i1:core_mem)
: Lemma 
  (requires
    disjoint i0 i1)
  (ensures
    level i0 == level i1 /\
    level (join i0 i1) == level i0 /\
    credits (join i0 i1) == credits i0 + credits i1)

let affine_prop (p: core_mem -> prop) =
  forall (m0 m1:core_mem). p m0 /\ disjoint m0 m1 ==> p (join m0 m1)

val interp (p:slprop) : q:(core_mem  -> prop) { affine_prop q }


val star_equiv :
      p:slprop ->
      q:slprop ->
      m:core_mem ->
      Lemma (
        interp (p `star` q) m <==> 
      (exists m0 m1. 
          disjoint m0 m1 /\
          m == join m0 m1 /\
          interp p m0 /\
          interp q m1))

val emp_equiv (m:core_mem) : Lemma (interp emp m)

val interp_exists (#a:Type u#a) (p: a -> slprop)
: Lemma (forall m. interp (op_exists_Star p) m <==> (exists x. interp (p x) m))

val interp_pure (p:prop) (m:core_mem)
: Lemma (interp (pure p) m <==> p)

let destruct_star_l (p q:slprop) (m:core_mem)
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


let destruct_star (p q:slprop) (m:core_mem)
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
                   PM.pulse_heap_sig.interp p m.pulse_mem)

val lift_emp_eq () : Lemma (
  lift PM.emp == emp
)
val lift_pure_eq (p:prop) : Lemma (
  lift (PM.pure p) == pure p
)
val lift_star_eq (p q:pm_slprop) : Lemma (
  lift (PM.star p q) == star (lift p) (lift q)
)
val lift_exists_eq (a:Type u#4) (f:a -> pm_slprop) : Lemma (
  lift PM.(h_exists #a f) == (exists* (x:a). lift (f x))
)

(**** Memory invariants *)
[@@erasable]
val iref : Type0
val deq_iref : FStar.GhostSet.decide_eq iref
let inames = FStar.GhostSet.set iref
val lower_inames (i:inames) : PM.inames

(** This proposition tells us that all the invariants names in [e] are valid in memory [m] *)
val istore_inames_ok (e:inames) (m:istore) : prop
let inames_ok (e:inames) (m:mem)
: prop
= HeapSig.inames_ok #PM.pulse_heap_sig (lower_inames e) m.pulse_mem /\
  istore_inames_ok e m.istore

(** The empty set of invariants is always empty *)
val inames_ok_empty (m:mem)
  : Lemma (ensures inames_ok GhostSet.empty m)
val inames_ok_union (i j:inames) (m:mem)
: Lemma 
  (inames_ok (FStar.GhostSet.union i j) m <==>
   inames_ok i m /\
   inames_ok j m)

val istore_invariant (ex:inames) (i:istore) : slprop

let mem_invariant (e:inames) (w:mem)
: slprop
=  lift (PM.mem_invariant (lower_inames e) w.pulse_mem) `star`
   istore_invariant e w.istore


val inv (i:iref) (p:slprop) : slprop
val later (p:slprop) : slprop
val later_credit (n:nat) : slprop
val equiv (p q:slprop) : slprop

val intro_later (p:slprop) (m:core_mem)
: Lemma (interp p m ==> interp (later p) m)
val istore_dom (m:mem) : inames

val age_mem (m:mem) : m':mem { 
  core_of m' == age1 (core_of m) /\
  is_ghost_action m m' /\
  (is_full m ==> is_full m') /\
  (istore_dom m == istore_dom m')
}
val age_level (m:core_mem)
: Lemma
  (requires level m > 0)
  (ensures level (age1 m) == level m - 1 /\
            credits (age1 m) == credits m)
val age_disjoint (m0 m1:core_mem)
: Lemma
  (requires disjoint m0 m1)
  (ensures 
    disjoint (age1 m0) (age1 m1) /\
    age1 (join m0 m1) == join (age1 m0) (age1 m1))
val age_hereditary (p:slprop) (m:core_mem)
: Lemma (interp p m ==> interp p (age1 m))
val age_later (p:slprop) (m:core_mem)
: Lemma 
  (requires level m > 0)
  (ensures interp (later p) m ==> interp p (age1 m))

val spend (m:core_mem) : core_mem
val spend_mem (m:mem) : m':mem { 
  core_of m' == spend (core_of m) /\
  is_ghost_action m m' /\
  (is_full m ==> is_full m') /\
  (istore_dom m == istore_dom m')
}
val interp_later_credit (n:nat) (m:core_mem)
: Lemma (interp (later_credit n) m <==> credits m >= n)
val spend_lemma (m:core_mem)
: Lemma 
  (requires
    credits m > 0)
  (ensures (
    let m' = spend m in
    level m' == level m /\
    credits m' == credits m - 1))
val spend_disjoint (m0 m1:core_mem)
: Lemma
  (requires
    disjoint m0 m1 /\
    credits m0 > 0)
  (ensures
    disjoint (spend m0) m1 /\
    spend (join m0 m1) == join (spend m0) m1)

val buy (n:nat) (m:core_mem) : core_mem
val buy_mem (n:FStar.Ghost.erased nat) (m:mem) : m':mem {
  core_of m' == buy n (core_of m) /\
  is_ghost_action m m' /\
  (is_full m ==> is_full m') /\
  (istore_dom m == istore_dom m')
}
val buy_lemma (n:nat) (m:core_mem)
: Lemma (
  let m' = buy n m in
  level m' == level m /\
  credits m' == credits m + n
)
val buy_disjoint (n:nat) (m0 m1:core_mem)
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

val iname_ok (i: iref) (m: core_mem) : prop
val inames_ok_single (i: iref) (p:slprop) (m:core_mem)
: Lemma
  (requires interp (inv i p) m)
  (ensures iname_ok i m)

val iname_ok_inames_ok (i:iref) (m:mem)
: Lemma (inames_ok (single i) m <==> iname_ok i (core_of m))
        [SMTPat (inames_ok (single i) m)]

val read_inv (i: iref) (m: core_mem { iname_ok i m }) : slprop
val read_inv_equiv (i:iref) (m:core_mem { iname_ok i m }) p 
: Lemma
  (requires 
    interp (inv i p) m)
  (ensures
    interp (later (read_inv i m)) m
    <==>
    interp (later p) m)

val read_inv_disjoint (i:iref) (m0 m1:core_mem)
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
      i:iref { iname_ok i (core_of m) } ->
      Lemma
        (requires
          ~(mem_inv e i))
        (ensures
          (mem_invariant e m ==
           mem_invariant (add_inv e i) m `star` later (read_inv i (core_of m))))


val inames_ok_istore_dom (e:inames) (m:mem)
: Lemma (inames_ok e m ==> FStar.GhostSet.subset e (istore_dom m))

val inames_ok_update (e:inames) (m0 m1:mem)
: Lemma 
  (requires istore_dom m0 == istore_dom m1)
  (ensures inames_ok e m0 <==> inames_ok e m1)

val join_mem (m0:mem) (m1:mem { disjoint (core_of m0) (core_of m1) })
: m:mem { core_of m == join (core_of m0) (core_of m1) }

val inames_ok_disjoint (i j:inames) (mi mj:mem)
: Lemma
  (requires
    disjoint (core_of mi) (core_of mj) /\
    inames_ok i mi /\
    inames_ok j mj)
  (ensures
    inames_ok (FStar.GhostSet.union i j) (join_mem mi mj))

val mem_invariant_disjoint (e f:inames) (p0 p1:slprop) (m0 m1:mem)
: Lemma
  (requires
    disjoint (core_of m0) (core_of m1) /\
    FStar.GhostSet.disjoint (istore_dom m0) (istore_dom m1) /\
    interp (p0 `star` mem_invariant e m0) (core_of m0) /\
    interp (p1 `star` mem_invariant f m1) (core_of m1))
  (ensures (
    let m = join_mem m0 m1 in
    interp (p0 `star` p1 `star` mem_invariant (FStar.GhostSet.union e f) m) (core_of m)))

val mem_invariant_age (e:inames) (m0:mem) (m1:core_mem)
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
    let c, c' = core_of m, core_of m' in
    fresh_wrt ctx i /\
    disjoint c c' /\
    is_ghost_action m (join_mem m m') /\
    (is_full m ==> is_full (join_mem m m')) /\
    inames_ok (single i) m' /\
    interp (inv i p `star` mem_invariant (single i) m') c' /\
    FStar.GhostSet.disjoint (istore_dom m) (istore_dom m') /\
    credits c' == 0
  }

val dup_inv_equiv :
    i:iref ->
    p:slprop ->
    Lemma (inv i p == (inv i p `star` inv i p))