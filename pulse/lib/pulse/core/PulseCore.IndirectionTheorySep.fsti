module PulseCore.IndirectionTheorySep
module F = FStar.FunctionalExtensionality
module T = FStar.Tactics
module PM = PulseCore.MemoryAlt

val istore : Type u#4
val core_istore : Type u#4
let pulse_mem_t : Type u#4 = PM.mem u#0
let pulse_core_mem_t : Type u#4 = PM.pulse_heap_sig.sep.core
noeq type world = { istore:istore; pulse_mem:PM.mem u#0 }
noeq type core_world = { istore:core_istore; pulse_mem:pulse_core_mem_t }
val world_heap_sig : hs:PulseCore.HeapSig.heap_sig u#3 {
  hs.mem == world /\
  hs.sep.core == core_world
}
let core_of (w:world) : core_world = world_heap_sig.sep.core_of w
val age1 (k:world) : world
val level (k:world) : GTot nat
val credits (k:world) : GTot nat
let is_ghost_action (m0 m1:world) : prop = world_heap_sig.is_ghost_action m0 m1

let is_full (w:world) : prop = world_heap_sig.full_mem_pred w
let full_world = w:world { is_full w }

let slprop : Type u#4 = world_heap_sig.slprop
let interpret (p:slprop) (w:world) : prop = world_heap_sig.interp p (core_of w)

let emp : slprop = world_heap_sig.emp
let pure (p:prop) : slprop = world_heap_sig.pure p
let star (p q:slprop) : slprop = world_heap_sig.star p q
val ( exists* ) (#a:Type u#a) (f:a -> slprop) : slprop

val sep_laws (_:unit) : squash (
  PulseCore.Semantics.(
    associative star /\
    commutative star /\
    is_unit emp star
  )
)

let pm_slprop : Type u#4 = PM.slprop u#0
val lift (p:pm_slprop) : slprop
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
let iref : Type0 = world_heap_sig.iref

(** Invariants have a name *)
let inames = FStar.GhostSet.set iref
val lower_inames (i:inames) : PM.inames

(** This proposition tells us that all the invariants names in [e] are valid in memory [m] *)
let inames_ok (e:inames) (m:world)
: prop
= HeapSig.inames_ok #world_heap_sig e m

(** The empty set of invariants is always empty *)
val inames_ok_empty (m:world)
  : Lemma (ensures inames_ok GhostSet.empty m)
          [SMTPat (inames_ok GhostSet.empty m)]


let world_invariant (e:inames) (w:world)
: slprop
= world_heap_sig.mem_invariant e w

let inv (i:iref) (p:slprop)
: slprop
= world_heap_sig.inv i p

val later (p:slprop) : slprop
val later_credit (n:nat) : slprop
val equiv (p q:slprop) : slprop