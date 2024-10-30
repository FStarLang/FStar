module PulseCore.IndirectionTheorySep
module I = PulseCore.IndirectionTheorySepImpl
open FStar.Ghost
module PropExt = FStar.PropositionalExtensionality

[@@erasable]
noeq type istore = {
  ist: I.okay_istore;
  saved_credits: erased nat;
  freshness_counter: nat;
}

[@@erasable]
noeq type core_istore = {
  ist: I.okay_istore;
  saved_credits: erased nat;
}

let to_core (w: I.world) : core_mem =
  { istore = { ist = fst w; saved_credits = (snd w).saved_credits }; pulse_mem = (snd w).pulse_heap }

let of_core (m: core_mem) : GTot I.world =
  (m.istore.ist, ({ saved_credits = m.istore.saved_credits; pulse_heap = m.pulse_mem } <: I.rest))

let istore_core i = { ist = i.ist; saved_credits = i.saved_credits }

let age1 k =
  { k with istore = { k.istore with ist = I.age1_istore k.istore.ist } }

let slprop = I.slprop

let ilevel k = I.level_istore k.ist
let level k = I.level_istore k.istore.ist

let level_depends_on_core_istore_only m = ()

let icredits k = k.saved_credits

let is_ghost_action_istore i1 i2 =
  i1.saved_credits >= i2.saved_credits /\
  i1.freshness_counter <= i2.freshness_counter

let update_ghost m1 m2 =
  { istore = (reveal m2).istore; pulse_mem = PM.pulse_heap_sig.update_ghost m1.pulse_mem (reveal m2).pulse_mem; }

let emp = I.emp
let pure = I.pure
let star = I.star

let (exists*) #a f = I.((exists*)) f

let sep_laws = I.sep_laws

let istore_disjoint i0 i1 = I.disjoint_istore i0.ist i1.ist

let istore_join i0 i1 =
  { ist = I.join_istore i0.ist i1.ist; saved_credits = i0.saved_credits + i1.saved_credits }

let istore_join_refl i = I.join_istore_refl i.ist

let disjoint_join_levels i0 i1 = ()

let interp p =
  introduce forall (m0 m1:core_mem). p (of_core m0) /\ disjoint m0 m1 ==> p (of_core (join m0 m1)) with
    introduce _ ==> _ with _.  assert I.world_le (of_core m0) (of_core (join m0 m1));
  fun m -> p (of_core m)

let star_equiv p q m = admit ()

let emp_equiv m = ()

let interp_exists p = ()

let interp_pure p m = ()

let lift p = I.lift p
let lift_eq p = ()
let lift_emp_eq () = I.lift_emp_eq ()
let lift_pure_eq p = I.lift_pure_eq p
let lift_star_eq p q = I.lift_star_eq p q
let lift_exists_eq a f =
  I.world_pred_ext (lift PM.(h_exists f)) (exists* x. lift (f x)) fun _ ->
    I.lift_exists_eq a f

let iref = I.iref
let deq_iref = fun x y -> reveal x = reveal y
let lower_inames i = GhostSet.empty

let istore_inames_ok e m = I.inames_ok e m.ist

let inames_ok_iff e (m: mem) : Lemma (inames_ok e m <==> istore_inames_ok e m.istore) [SMTPat (inames_ok e m)] =
  ()

let inames_ok_empty m = ()
let inames_ok_union m = admit ()

let istore_invariant ex i = admit ()

let inv i p = I.inv i p

let later p = I.later p
let later_credit n = I.later_credit n
let equiv = I.equiv

let intro_later p m = ()

let istore_dom m = I.istore_dom m.istore.ist

let pulse_ghost_action_refl m : Lemma (PM.is_ghost_action m m) [SMTPat (PM.is_ghost_action m m)] =
  PM.pulse_heap_sig.is_ghost_action_preorder ()

let age_mem m =
  let m': mem = { m with istore = { m.istore with ist = I.age1_istore m.istore.ist } } in
  GhostSet.lemma_equal_intro (istore_dom m) (istore_dom m'); assert istore_dom m == istore_dom m';
  m'

let age_level m = ()

let age_disjoint m0 m1 = ()

let age_hereditary p m =
  assert of_core (age1 m) == I.age1_ (of_core m)

let age_later p m = ()

let spend m =
  { m with istore = { m.istore with
    saved_credits = if m.istore.saved_credits > 0 then m.istore.saved_credits - 1 else 0 } }

let spend_mem m =
  { m with istore = { m.istore with
    saved_credits = if m.istore.saved_credits > 0 then m.istore.saved_credits - 1 else 0 } }

let interp_later_credit n m = ()

let spend_lemma m = ()

let spend_disjoint m0 m1 = ()

let buy n m = { m with istore = { m.istore with saved_credits = m.istore.saved_credits + n } }
let buy_mem n m = { m with istore = { m.istore with saved_credits = m.istore.saved_credits + n } }
let buy_lemma n m = ()
let buy_disjoint n m0 m1 = ()

let mem_invariant_equiv e m i p = admit ()

let inames_ok_istore_dom e m = ()

let inames_ok_update e m0 m1 =
  assert forall i. GhostSet.mem i (istore_dom m0) <==> GhostSet.mem i (istore_dom m1)

let join_mem m0 m1 = admit ()

let inames_ok_disjoint = admit ()

let mem_invariant_disjoint e f p0 p1 m0 m1 = admit ()

let mem_invariant_age e m = ()
let mem_invariant_spend e m = ()

let fresh_inv p m ctx = admit ()

let dup_inv_equiv i p = admit ()
