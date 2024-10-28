module PulseCore.IndirectionTheorySep
module F = FStar.FunctionalExtensionality
module T = FStar.Tactics
module PM = PulseCore.MemoryAlt

val world : Type u#4
val age1 (k:world) : world
val level (k:world) : GTot nat
val credits (k:world) : GTot nat
val is_ghost_action (m0 m1:world) : prop //preorder

val ghost_action_preorder (_:unit)
  : Lemma (FStar.Preorder.preorder_rel is_ghost_action)
  
val is_full : world -> prop
let full_world = w:world { is_full w }

[@@erasable]
val slprop : Type u#4
val interp (p:slprop) : world -> prop
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

val lift (p:PM.slprop) : slprop
val lift_emp_eq () : Lemma (
  lift PM.emp == emp
)
val lift_pure_eq (p:prop) : Lemma (
  lift (PM.pure p) == pure p
)
val lift_star_eq (p q:PM.slprop) : Lemma (
  lift (PM.star p q) == star (lift p) (lift q)
)
val lift_exists_eq (a:Type u#4) (f:a -> PM.slprop) : Lemma (
  lift PM.(h_exists #a f) == (exists* (x:a). lift (f x))
)

(**** Memory invariants *)
[@@erasable]
val iref : Type0
val deq_iref : FStar.GhostSet.decide_eq iref

(** Invariants have a name *)
let inames = FStar.GhostSet.set iref
val lower_inames (i:inames) : PM.inames

(** This proposition tells us that all the invariants names in [e] are valid in memory [m] *)
val inames_ok (e:inames) (m:world) : prop

(** The empty set of invariants is always empty *)
val inames_ok_empty (m:world)
  : Lemma (ensures inames_ok GhostSet.empty m)
          [SMTPat (inames_ok GhostSet.empty m)]


val world_invariant (e:inames) (w:world) : slprop //Needed tor interpreter
val inv (i:iref) (p:slprop) : slprop
val later (p:slprop) : slprop
val later_credit (n:nat) : slprop
val equiv (p q:slprop) : slprop