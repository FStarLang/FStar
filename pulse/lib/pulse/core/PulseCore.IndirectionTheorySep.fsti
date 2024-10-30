module PulseCore.IndirectionTheorySep
module F = FStar.FunctionalExtensionality
module T = FStar.Tactics
module PM = PulseCore.MemoryAlt

val istore : Type u#4
val core_istore : Type u#4
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

val level (k:core_mem) : GTot nat

val credits (k:core_istore) : GTot nat
let has_credits (m:mem) : GTot bool = credits (istore_core m.istore) > 0

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
val istore_join_refl (i:core_istore { credits i == 0 }) 
: Lemma (istore_disjoint i i /\ istore_join i i == i)
let disjoint (m0 m1:core_mem)
: prop
= PM.pulse_heap_sig.sep.disjoint m0.pulse_mem m1.pulse_mem /\
  istore_disjoint m0.istore m1.istore
let join (m0:core_mem) (m1:core_mem { disjoint m0 m1 })
: core_mem
= { pulse_mem = PM.pulse_heap_sig.sep.join m0.pulse_mem m1.pulse_mem;
    istore = istore_join m0.istore m1.istore }

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

let single (i:iref) : inames = FStar.GhostSet.singleton deq_iref i
let add_inv (e:inames) (i:iref)
: inames
= FStar.GhostSet.(union (single i) e)

let mem_inv (e:inames) (i:iref)
: GTot bool
= GhostSet.mem i e

val mem_invariant_equiv : 
      e:inames ->
      m:mem ->
      i:iref ->
      p:slprop ->
      Lemma 
        (requires
          interp (inv i p) (core_of m) /\
          ~(mem_inv e i))
        (ensures
          inames_ok (single i) m /\
          (mem_invariant e m ==
           mem_invariant (add_inv e i) m `star` later p))

val istore_dom (m:mem) : inames

val inames_ok_istore_dom (e:inames) (m:mem)
: Lemma (inames_ok e m ==> FStar.GhostSet.subset e (istore_dom m))

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
    FStar.GhostSet.disjoint (istore_dom m) (istore_dom m')
  }

val dup_inv_equiv :
    i:iref ->
    p:slprop ->
    Lemma (inv i p == (inv i p `star` inv i p))